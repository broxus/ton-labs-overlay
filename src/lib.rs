use std::sync::atomic::{AtomicBool, AtomicU32, Ordering};
use std::sync::Arc;
use std::time::Duration;

use adnl::common::*;
use adnl::node::{AddressCache, AdnlNode, IpAddress, PeerHistory};
use dashmap::{DashMap, DashSet};
use rldp::{RaptorqDecoder, RaptorqEncoder, RldpNode};
use sha2::Digest;
use tokio::sync::mpsc;
use ton_api::ton::adnl::id::short::Short as AdnlShortId;
use ton_api::ton::catchain::blockupdate::BlockUpdate as CatchainBlockUpdate;
use ton_api::ton::catchain::FirstBlock as CatchainFirstBlock;
use ton_api::ton::catchain::Update as CatchainBlockUpdateBoxed;
use ton_api::ton::fec::{type_::RaptorQ as FecTypeRaptorQ, Type as FecType};
use ton_api::ton::overlay::broadcast::id::Id as BroadcastOrdId;
use ton_api::ton::overlay::broadcast::tosign::ToSign as BroadcastToSign;
use ton_api::ton::overlay::broadcast::Broadcast as BroadcastOrd;
use ton_api::ton::overlay::broadcast::BroadcastFec;
use ton_api::ton::overlay::broadcast_fec::id::Id as BroadcastFecId;
use ton_api::ton::overlay::broadcast_fec::partid::PartId as BroadcastFecPartId;
use ton_api::ton::overlay::message::Message as OverlayMessage;
use ton_api::ton::overlay::node::{tosign::ToSign as NodeToSign, Node};
use ton_api::ton::overlay::nodes::Nodes;
use ton_api::ton::overlay::Broadcast;
use ton_api::ton::overlay::Certificate as OverlayCertificate;
use ton_api::ton::overlay::Message as OverlayMessageBoxed;
use ton_api::ton::overlay::Nodes as NodesBoxed;
use ton_api::ton::pub_::publickey::{Ed25519, Overlay};
use ton_api::ton::rpc::overlay::{GetRandomPeers, Query as OverlayQuery};
use ton_api::ton::ton_node::shardpublicoverlayid::ShardPublicOverlayId;
use ton_api::ton::validator_session::blockupdate::BlockUpdate as ValidatorSessionBlockUpdate;
use ton_api::ton::validator_session::BlockUpdate as ValidatorSessionBlockUpdateBoxed;
use ton_api::{ton, ton::TLObject, IntoBoxed};
use ton_types::{error, fail, Result};

const TARGET: &str = "overlay";

pub fn build_overlay_node_info(
    overlay: &Arc<OverlayShortId>,
    version: i32,
    key: &str,
    signature: &str,
) -> Result<Node> {
    let key = base64::decode(key)?;
    if key.len() != 32 {
        fail!("Bad public key length")
    }
    let signature = base64::decode(signature)?;
    let node = Node {
        id: Ed25519 {
            key: ton::int256(*arrayref::array_ref!(&key, 0, 32)),
        }
        .into_boxed(),
        overlay: ton::int256(*overlay.data()),
        version,
        signature: ton::bytes(signature),
    };
    Ok(node)
}

struct BroadcastReceiver<T> {
    data: lockfree::queue::Queue<T>,
    subscribers: lockfree::queue::Queue<Arc<tokio::sync::Barrier>>,
    synclock: AtomicU32,
}

impl<T: Send + 'static> BroadcastReceiver<T> {
    fn push(receiver: &Arc<Self>, data: T) {
        let receiver = receiver.clone();
        tokio::spawn(async move {
            receiver.data.push(data);
            while receiver.synclock.load(Ordering::Acquire) > 0 {
                if let Some(subscriber) = receiver.subscribers.pop() {
                    subscriber.wait().await;
                    break;
                } else {
                    tokio::task::yield_now().await;
                }
            }
        });
    }

    async fn pop(&self) -> Result<T> {
        self.synclock.fetch_add(1, Ordering::Release);
        loop {
            if let Some(data) = self.data.pop() {
                self.synclock.fetch_sub(1, Ordering::Release);
                return Ok(data);
            } else {
                let subscriber = Arc::new(tokio::sync::Barrier::new(2));
                self.subscribers.push(subscriber.clone());
                subscriber.wait().await;
            }
        }
    }
}

pub struct BroadcastRecvInfo {
    pub packets: u32,
    pub data: Vec<u8>,
    pub recv_from: Arc<KeyId>,
}

#[derive(Debug, Default)]
pub struct BroadcastSendInfo {
    pub packets: u32,
    pub send_to: u32,
}

pub type OverlayId = [u8; 32];
pub type OverlayShortId = KeyId;
pub type PrivateOverlayShortId = KeyId;

/// Overlay utilities
pub struct OverlayUtils;

impl OverlayUtils {
    /// Calculate overlay ID for shard
    pub fn calc_overlay_id(
        workchain: i32,
        _shard: i64,
        zero_state_file_hash: &[u8; 32],
    ) -> Result<OverlayId> {
        let overlay = ShardPublicOverlayId {
            shard: 1i64 << 63,
            workchain,
            zero_state_file_hash: ton::int256(*zero_state_file_hash),
        };
        hash(overlay)
    }

    /// Calculate overlay short ID for shard
    pub fn calc_overlay_short_id(
        workchain: i32,
        shard: i64,
        zero_state_file_hash: &[u8; 32],
    ) -> Result<Arc<OverlayShortId>> {
        let overlay = Overlay {
            name: ton::bytes(
                Self::calc_overlay_id(workchain, shard, zero_state_file_hash)?.to_vec(),
            ),
        };
        Ok(OverlayShortId::from_data(hash(overlay)?))
    }

    pub fn calc_private_overlay_short_id(
        first_block: &CatchainFirstBlock,
    ) -> Result<Arc<PrivateOverlayShortId>> {
        let serialized_first_block = serialize(first_block)?;
        let overlay_id = Overlay {
            name: serialized_first_block.into(),
        };
        let id = hash_boxed(&overlay_id.into_boxed())?;
        Ok(PrivateOverlayShortId::from_data(id))
    }

    /// Verify node info
    pub fn verify_node(overlay_id: &Arc<OverlayShortId>, node: &Node) -> Result<()> {
        let key = KeyOption::from_tl_public_key(&node.id)?;
        if get256(&node.overlay) != overlay_id.data() {
            fail!(
                "Got peer {} with wrong overlay {}, expected {}",
                key.id(),
                base64::encode(get256(&node.overlay)),
                overlay_id
            )
        }
        let node_to_sign = NodeToSign {
            id: AdnlShortId {
                id: ton::int256(*key.id().data()),
            },
            overlay: node.overlay,
            version: node.version,
        }
        .into_boxed();
        if let Err(e) = key.verify(&serialize(&node_to_sign)?, &node.signature) {
            fail!("Got peer {} with bad signature: {}", key.id(), e)
        }
        Ok(())
    }
}

type BroadcastId = [u8; 32];
type CatchainReceiver =
    BroadcastReceiver<(CatchainBlockUpdate, ValidatorSessionBlockUpdate, Arc<KeyId>)>;

enum OwnedBroadcast {
    Other,
    RecvFec(RecvTransferFec),
    WillBeRecvFec,
}

struct OverlayShard {
    adnl: Arc<AdnlNode>,
    bad_peers: DashSet<Arc<KeyId>>,
    known_peers: AddressCache,
    message_prefix: Vec<u8>,
    neighbours: AddressCache,
    nodes: DashMap<Arc<KeyId>, Node>,
    overlay_id: Arc<OverlayShortId>,
    overlay_key: Option<Arc<KeyOption>>,
    owned_broadcasts: DashMap<BroadcastId, OwnedBroadcast>,
    purge_broadcasts: lockfree::queue::Queue<BroadcastId>,
    purge_broadcasts_count: AtomicU32,
    query_prefix: Vec<u8>,
    random_peers: AddressCache,
    received_catchain: Option<Arc<CatchainReceiver>>,
    received_peers: Arc<BroadcastReceiver<Vec<Node>>>,
    received_rawbytes: Arc<BroadcastReceiver<BroadcastRecvInfo>>,
    // For debug
    debug_trace: AtomicU32,
}

impl OverlayShard {
    const SIZE_BROADCAST_WAVE: u32 = 20;
    const SPINNER: u64 = 10; // Milliseconds
    const TIMEOUT_BROADCAST: u64 = 100; // Seconds
    const FLAG_BCAST_ANY_SENDER: i32 = 1;

    fn calc_broadcast_id(&self, data: &[u8]) -> Option<BroadcastId> {
        use dashmap::mapref::entry::Entry;

        let bcast_id = sha2::Sha256::digest(data);
        let bcast_id = arrayref::array_ref!(bcast_id.as_slice(), 0, 32);

        match self.owned_broadcasts.entry(*bcast_id) {
            Entry::Vacant(entry) => {
                entry.insert(OwnedBroadcast::Other);
                Some(*bcast_id)
            }
            Entry::Occupied(_) => None,
        }
    }

    fn calc_broadcast_to_sign(data: &[u8], date: i32, src: [u8; 32]) -> Result<Vec<u8>> {
        let data_hash = sha2::Sha256::digest(data);
        let data_hash = *arrayref::array_ref!(data_hash.as_slice(), 0, 32);
        let bcast_id = BroadcastOrdId {
            src: ton::int256(src),
            data_hash: ton::int256(data_hash),
            flags: Self::FLAG_BCAST_ANY_SENDER,
        };
        let data_hash = hash(bcast_id)?;
        let to_sign = BroadcastToSign {
            hash: ton::int256(data_hash),
            date,
        }
        .into_boxed();
        serialize(&to_sign)
    }

    #[allow(clippy::too_many_arguments)]
    fn calc_fec_part_to_sign(
        data_hash: &[u8; 32],
        data_size: i32,
        date: i32,
        flags: i32,
        params: &FecTypeRaptorQ,
        part: &[u8],
        seqno: i32,
        src: [u8; 32],
    ) -> Result<Vec<u8>> {
        let broadcast_id = BroadcastFecId {
            src: ton::int256(src),
            type_: ton::int256(hash(params.clone())?),
            data_hash: ton::int256(*data_hash),
            size: data_size,
            flags,
        };
        let broadcast_hash = hash(broadcast_id)?;
        let part_data_hash = sha2::Sha256::digest(part);
        let part_data_hash = *arrayref::array_ref!(part_data_hash.as_slice(), 0, 32);

        let part_id = BroadcastFecPartId {
            broadcast_hash: ton::int256(broadcast_hash),
            data_hash: ton::int256(part_data_hash),
            seqno,
        };
        let part_hash = hash(part_id)?;

        let to_sign = BroadcastToSign {
            hash: ton::int256(part_hash),
            date,
        }
        .into_boxed();
        serialize(&to_sign)
    }

    fn create_fec_recv_transfer(
        overlay_shard: &Arc<Self>,
        bcast: &BroadcastFec,
    ) -> Result<RecvTransferFec> {
        let fec_type = if let FecType::Fec_RaptorQ(fec_type) = &bcast.fec {
            fec_type
        } else {
            fail!("Unsupported FEC type")
        };

        let overlay_shard_recv = overlay_shard.clone();
        let bcast_id_recv = *get256(&bcast.data_hash);
        let (sender, mut reader) = mpsc::unbounded_channel::<Box<BroadcastFec>>();
        let mut decoder = RaptorqDecoder::with_params(fec_type.as_ref().clone());
        let overlay_shard_wait = overlay_shard_recv.clone();
        let bcast_id_wait = bcast_id_recv;
        let source = KeyOption::from_tl_public_key(&bcast.src)?.id().clone();
        let source_recv = source.clone();

        tokio::spawn(async move {
            let mut packets = 0;
            while let Some(bcast) = reader.recv().await {
                packets += 1;
                match Self::process_fec_broadcast(&mut decoder, &bcast) {
                    Err(err) => log::warn!(
                        target: TARGET,
                        "Error when receiving overlay {} broadcast: {}",
                        overlay_shard_recv.overlay_id,
                        err
                    ),
                    Ok(Some(data)) => BroadcastReceiver::push(
                        &overlay_shard_recv.received_rawbytes,
                        BroadcastRecvInfo {
                            packets,
                            data,
                            recv_from: source_recv,
                        },
                    ),
                    Ok(None) => continue,
                }
                break;
            }
            if let Some(transfer) = overlay_shard_recv.owned_broadcasts.get(&bcast_id_recv) {
                if let OwnedBroadcast::RecvFec(transfer) = transfer.value() {
                    transfer.completed.store(true, Ordering::Release);
                } else {
                    log::error!(
                        target: TARGET,
                        "INTERNAL ERROR: recv FEC broadcast {} mismatch in overlay {}",
                        base64::encode(&bcast_id_recv),
                        overlay_shard_recv.overlay_id
                    )
                }
            }
            // Graceful close
            reader.close();
            while reader.recv().await.is_some() {}
        });

        tokio::spawn(async move {
            loop {
                tokio::time::sleep(Duration::from_millis(Self::TIMEOUT_BROADCAST * 100)).await;
                if let Some(transfer) = overlay_shard_wait.owned_broadcasts.get(&bcast_id_wait) {
                    if let OwnedBroadcast::RecvFec(transfer) = transfer.value() {
                        if !transfer.updated_at.is_expired(Self::TIMEOUT_BROADCAST) {
                            continue;
                        }
                    } else {
                        log::error!(
                            target: TARGET,
                            "INTERNAL ERROR: recv FEC broadcast {} mismatch in overlay {}",
                            base64::encode(&bcast_id_wait),
                            overlay_shard_wait.overlay_id
                        )
                    }
                }
                break;
            }
            Self::setup_broadcast_purge(&overlay_shard_wait, bcast_id_wait);
        });

        let ret = RecvTransferFec {
            completed: AtomicBool::new(false),
            history: PeerHistory::new(),
            sender,
            source,
            updated_at: UpdatedAt::new(),
        };
        Ok(ret)
    }

    fn create_fec_send_transfer(
        overlay_shard: &Arc<Self>,
        data: &[u8],
        source: &Arc<KeyOption>,
        overlay_key: &Arc<KeyId>,
    ) -> Result<BroadcastSendInfo> {
        let overlay_shard_clone = overlay_shard.clone();
        let source = source.clone();
        let (sender, mut reader) = mpsc::unbounded_channel();

        let data_size = data.len() as u32;
        let bcast_id = match overlay_shard.calc_broadcast_id(data) {
            Some(bcast_id) => bcast_id,
            None => return Ok(BroadcastSendInfo::default()),
        };
        let mut transfer = SendTransferFec {
            bcast_id,
            encoder: RaptorqEncoder::with_data(data),
            seqno: 0,
        };
        let max_seqno = (data_size / transfer.encoder.params().symbol_size as u32 + 1) * 3 / 2;

        tokio::spawn(async move {
            while transfer.seqno <= max_seqno {
                for _ in 0..Self::SIZE_BROADCAST_WAVE {
                    let result = overlay_shard_clone
                        .prepare_fec_broadcast(&mut transfer, &source)
                        .and_then(|data| {
                            sender.send(data)?;
                            Ok(())
                        });
                    if let Err(err) = result {
                        log::warn!(
                            target: TARGET,
                            "Error when sending overlay {} broadcast: {}",
                            overlay_shard_clone.overlay_id,
                            err
                        );
                        return;
                    }
                    if transfer.seqno > max_seqno {
                        break;
                    }
                }
                tokio::time::sleep(Duration::from_millis(Self::SPINNER)).await;
            }
        });

        let overlay_shard = overlay_shard.clone();
        let overlay_key = overlay_key.clone();

        let neighbours = overlay_shard.neighbours.random_vec(None, 5);
        let ret = BroadcastSendInfo {
            packets: max_seqno,
            send_to: neighbours.len() as u32,
        };

        tokio::spawn(async move {
            while let Some(buf) = reader.recv().await {
                if let Err(err) = overlay_shard
                    .distribute_broadcast(&buf, &overlay_key, &neighbours)
                    .await
                {
                    log::warn!(
                        target: TARGET,
                        "Error when sending overlay {} FEC broadcast: {}",
                        overlay_shard.overlay_id,
                        err
                    );
                }
            }
            // Graceful close
            reader.close();
            while reader.recv().await.is_some() {}
            Self::setup_broadcast_purge(&overlay_shard, bcast_id);
        });
        Ok(ret)
    }

    async fn distribute_broadcast(
        &self,
        data: &[u8],
        key: &Arc<KeyId>,
        neighbours: &[Arc<KeyId>],
    ) -> Result<()> {
        log::trace!(
            target: TARGET,
            "Broadcast {} bytes to overlay {}, {} neighbours",
            data.len(),
            self.overlay_id,
            neighbours.len()
        );
        let mut peers: Option<AdnlPeers> = None;

        for neighbour in neighbours.iter() {
            let peers = if let Some(peers) = &mut peers {
                peers.set_other(neighbour.clone());
                peers
            } else {
                peers.get_or_insert_with(|| AdnlPeers::with_keys(key.clone(), neighbour.clone()))
            };

            if let Err(e) = self.adnl.send_custom(data, peers).await {
                log::warn!(
                    target: TARGET,
                    "Broadcast {} bytes to overlay {}, wasn't send to {}: {}",
                    data.len(),
                    self.overlay_id,
                    neighbour,
                    e
                )
            }
        }

        Ok(())
    }

    fn is_broadcast_outdated(&self, date: i32, peer: &Arc<KeyId>) -> bool {
        let now = now();
        if date + (Self::TIMEOUT_BROADCAST as i32) < now {
            log::warn!(
                target: TARGET,
                "Old FEC broadcast {} seconds old from {} in overlay {}",
                now - date,
                peer,
                self.overlay_id
            );
            true
        } else {
            false
        }
    }

    fn prepare_fec_broadcast(
        &self,
        transfer: &mut SendTransferFec,
        key: &Arc<KeyOption>,
    ) -> Result<Vec<u8>> {
        let chunk = transfer.encoder.encode(&mut transfer.seqno)?;
        let date = now();
        let signature = Self::calc_fec_part_to_sign(
            &transfer.bcast_id,
            transfer.encoder.params().data_size,
            date,
            Self::FLAG_BCAST_ANY_SENDER,
            transfer.encoder.params(),
            &chunk,
            transfer.seqno as i32,
            [0u8; 32],
        )?;
        let signature = key.sign(&signature)?;

        let bcast = BroadcastFec {
            src: key.as_tl_public_key()?,
            certificate: OverlayCertificate::Overlay_EmptyCertificate,
            data_hash: ton::int256(transfer.bcast_id),
            data_size: transfer.encoder.params().data_size,
            flags: Self::FLAG_BCAST_ANY_SENDER,
            data: ton::bytes(chunk),
            seqno: transfer.seqno as i32,
            fec: transfer.encoder.params().clone().into_boxed(),
            date,
            signature: ton::bytes(signature.to_vec()),
        }
        .into_boxed();

        transfer.seqno += 1;
        let mut buf = self.message_prefix.clone();
        serialize_append(&mut buf, &bcast)?;
        Ok(buf)
    }

    fn process_fec_broadcast(
        decoder: &mut RaptorqDecoder,
        bcast: &BroadcastFec,
    ) -> Result<Option<Vec<u8>>> {
        let fec_type = if let FecType::Fec_RaptorQ(fec_type) = &bcast.fec {
            fec_type
        } else {
            fail!("Unsupported FEC type")
        };

        let src_key = KeyOption::from_tl_public_key(&bcast.src)?;
        let src = if (bcast.flags & Self::FLAG_BCAST_ANY_SENDER) != 0 {
            [0u8; 32]
        } else {
            *src_key.id().data()
        };

        let bcast_id = get256(&bcast.data_hash);
        let signature = Self::calc_fec_part_to_sign(
            bcast_id,
            bcast.data_size,
            bcast.date,
            bcast.flags,
            fec_type,
            &bcast.data,
            bcast.seqno,
            src,
        )?;
        src_key.verify(&signature, &bcast.signature.0)?;

        if let Some(ret) = decoder.decode(bcast.seqno as u32, &bcast.data) {
            if ret.len() != bcast.data_size as usize {
                fail!(
                    "Expected {} bytes, but received {}",
                    bcast.data_size,
                    ret.len()
                )
            } else {
                let test_id = sha2::Sha256::digest(&ret);
                if test_id.as_slice() != bcast_id {
                    fail!(
                        "Expected {} broadcast hash, but received {}",
                        base64::encode(test_id.as_slice()),
                        base64::encode(bcast_id)
                    )
                }
                log::trace!(
                    target: TARGET,
                    "Received overlay broadcast {} ({} bytes)",
                    base64::encode(bcast_id),
                    ret.len()
                )
            }
            Ok(Some(ret))
        } else {
            Ok(None)
        }
    }

    async fn receive_broadcast(
        overlay_shard: &Arc<Self>,
        bcast: Box<BroadcastOrd>,
        raw_data: &[u8],
        peers: &AdnlPeers,
    ) -> Result<()> {
        if overlay_shard.is_broadcast_outdated(bcast.date, peers.other()) {
            return Ok(());
        }
        let src_key = KeyOption::from_tl_public_key(&bcast.src)?;
        let src = if (bcast.flags & Self::FLAG_BCAST_ANY_SENDER) != 0 {
            [0u8; 32]
        } else {
            *src_key.id().data()
        };
        let signature = Self::calc_broadcast_to_sign(&bcast.data, bcast.date, src)?;
        let bcast_id = match overlay_shard.calc_broadcast_id(&signature) {
            Some(bcast_id) => bcast_id,
            None => return Ok(()),
        };
        src_key.verify(&signature, &bcast.signature.0)?;
        let ton::bytes(data) = bcast.data;
        log::trace!(
            target: TARGET,
            "Received overlay broadcast, {} bytes",
            data.len()
        );

        BroadcastReceiver::push(
            &overlay_shard.received_rawbytes,
            BroadcastRecvInfo {
                packets: 1,
                data,
                recv_from: src_key.id().clone(),
            },
        );
        let neighbours = overlay_shard.neighbours.random_vec(Some(peers.other()), 3);
        // Transit broadcasts will be traced untagged
        overlay_shard
            .distribute_broadcast(raw_data, peers.local(), &neighbours)
            .await?;
        Self::setup_broadcast_purge(overlay_shard, bcast_id);
        Ok(())
    }

    async fn receive_fec_broadcast(
        overlay_shard: &Arc<Self>,
        bcast: Box<BroadcastFec>,
        raw_data: &[u8],
        peers: &AdnlPeers,
    ) -> Result<()> {
        use dashmap::mapref::entry::Entry;

        if overlay_shard.is_broadcast_outdated(bcast.date, peers.other()) {
            return Ok(());
        }
        let broadcast_id = get256(&bcast.data_hash);

        let transfer = loop {
            if let Some(transfer) = overlay_shard.owned_broadcasts.get(broadcast_id) {
                break transfer;
            }

            match overlay_shard.owned_broadcasts.entry(*broadcast_id) {
                Entry::Vacant(entry) => {
                    entry.insert(OwnedBroadcast::WillBeRecvFec);
                }
                Entry::Occupied(_) => {
                    tokio::task::yield_now().await;
                    continue;
                }
            }

            let transfer = Self::create_fec_recv_transfer(overlay_shard, &bcast);
            if transfer.is_err() {
                overlay_shard.owned_broadcasts.remove(broadcast_id);
            }
            let transfer = OwnedBroadcast::RecvFec(transfer?);
            let ok = matches!(
                overlay_shard
                    .owned_broadcasts
                    .insert(*broadcast_id, transfer),
                Some(OwnedBroadcast::WillBeRecvFec)
            );
            if !ok {
                log::error!(
                    target: TARGET,
                    "INTERNAL ERROR: recv FEC broadcast {} creation mismatch in overlay {}",
                    base64::encode(broadcast_id),
                    overlay_shard.overlay_id
                )
            }
        };
        let transfer = transfer.value();
        let transfer = if let OwnedBroadcast::RecvFec(transfer) = transfer {
            transfer
        } else {
            // Not a receive FEC broadcast
            return Ok(());
        };
        transfer.updated_at.refresh();
        if &transfer.source != KeyOption::from_tl_public_key(&bcast.src)?.id() {
            log::warn!(
                target: TARGET,
                "Same broadcast {} but parts from different sources",
                base64::encode(broadcast_id)
            );
            return Ok(());
        }
        if !transfer.history.update(bcast.seqno as u64).await? {
            return Ok(());
        }

        if !transfer.completed.load(Ordering::Acquire) {
            transfer.sender.send(bcast)?;
        }
        let neighbours = overlay_shard.neighbours.random_vec(Some(peers.other()), 5);

        // Transit broadcasts will be traced untagged
        overlay_shard
            .distribute_broadcast(raw_data, peers.local(), &neighbours)
            .await?;
        Ok(())
    }

    async fn send_broadcast(
        overlay_shard: &Arc<Self>,
        data: &[u8],
        source: &Arc<KeyOption>,
        overlay_key: &Arc<KeyId>,
    ) -> Result<BroadcastSendInfo> {
        let date = now();
        let signature = Self::calc_broadcast_to_sign(data, date, [0u8; 32])?;
        let bcast_id = match overlay_shard.calc_broadcast_id(&signature) {
            Some(bcast_id) => bcast_id,
            None => {
                log::warn!(target: TARGET, "Trying to send duplicated broadcast");
                return Ok(BroadcastSendInfo::default());
            }
        };

        let signature = source.sign(&signature)?;
        let bcast = BroadcastOrd {
            src: source.as_tl_public_key()?,
            certificate: OverlayCertificate::Overlay_EmptyCertificate,
            flags: Self::FLAG_BCAST_ANY_SENDER,
            data: ton::bytes(data.to_vec()),
            date: now(),
            signature: ton::bytes(signature.to_vec()),
        }
        .into_boxed();
        let mut buf = overlay_shard.message_prefix.clone();
        serialize_append(&mut buf, &bcast)?;
        let neighbours = overlay_shard.neighbours.random_vec(None, 3);
        overlay_shard
            .distribute_broadcast(&buf, overlay_key, &neighbours)
            .await?;
        Self::setup_broadcast_purge(overlay_shard, bcast_id);
        let ret = BroadcastSendInfo {
            packets: 1,
            send_to: neighbours.len() as u32,
        };
        Ok(ret)
    }

    fn setup_broadcast_purge(overlay_shard: &Arc<Self>, bcast_id: BroadcastId) {
        let overlay_shard = overlay_shard.clone();
        tokio::spawn(async move {
            tokio::time::sleep(Duration::from_secs(Self::TIMEOUT_BROADCAST)).await;
            overlay_shard
                .purge_broadcasts_count
                .fetch_add(1, Ordering::Release);
            overlay_shard.purge_broadcasts.push(bcast_id);
        });
    }

    fn update_neighbours(&self, n: u32) -> Result<()> {
        if self.overlay_key.is_some() {
            self.known_peers.random_set(&self.neighbours, None, n)
        } else {
            self.random_peers
                .random_set(&self.neighbours, Some(&self.bad_peers), n)
        }
    }

    fn update_random_peers(&self, n: u32) -> Result<()> {
        self.known_peers
            .random_set(&self.random_peers, Some(&self.bad_peers), n)?;
        self.update_neighbours(OverlayNode::MAX_SHARD_NEIGHBOURS)
    }
}

struct RecvTransferFec {
    completed: AtomicBool,
    history: PeerHistory,
    sender: mpsc::UnboundedSender<Box<BroadcastFec>>,
    source: Arc<KeyId>,
    updated_at: UpdatedAt,
}

struct SendTransferFec {
    bcast_id: BroadcastId,
    encoder: RaptorqEncoder,
    seqno: u32,
}

#[async_trait::async_trait]
pub trait QueriesConsumer: Send + Sync {
    async fn try_consume_query(&self, query: TLObject, peers: &AdnlPeers) -> Result<QueryResult>;
}

/// Overlay Node
pub struct OverlayNode {
    adnl: Arc<AdnlNode>,
    node_key: Arc<KeyOption>,
    shards: DashMap<Arc<OverlayShortId>, Arc<OverlayShard>>,
    consumers: DashMap<Arc<OverlayShortId>, Arc<dyn QueriesConsumer>>,
    zero_state_file_hash: [u8; 32],
}

impl OverlayNode {
    const MAX_BROADCAST_LOG: u32 = 1000;
    const MAX_PEERS: u32 = 65536;
    const MAX_RANDOM_PEERS: u32 = 4;
    const MAX_SHARD_NEIGHBOURS: u32 = 5;
    const MAX_SHARD_PEERS: u32 = 20;
    const MAX_SIZE_ORDINARY_BROADCAST: usize = 768;
    const TIMEOUT_GC: u64 = 1000; // Milliseconds
    const TIMEOUT_PEERS: u64 = 60000; // Milliseconds

    /// Constructor
    pub fn with_adnl_node_and_zero_state(
        adnl: Arc<AdnlNode>,
        zero_state_file_hash: &[u8; 32],
        key_tag: usize,
    ) -> Result<Arc<Self>> {
        let node_key = adnl.key_by_tag(key_tag)?;
        Ok(Arc::new(Self {
            adnl,
            node_key,
            shards: DashMap::new(),
            consumers: DashMap::new(),
            zero_state_file_hash: *zero_state_file_hash,
        }))
    }

    /// Add overlay query consumer
    pub fn add_consumer(
        &self,
        overlay_id: &Arc<OverlayShortId>,
        consumer: Arc<dyn QueriesConsumer>,
    ) -> bool {
        use dashmap::mapref::entry::Entry;

        log::debug!(target: TARGET, "Add consumer {} to overlay", overlay_id);

        match self.consumers.entry(overlay_id.clone()) {
            Entry::Vacant(entry) => {
                entry.insert(consumer.clone());
                true
            }
            Entry::Occupied(_) => false,
        }
    }

    /// Add private_overlay
    pub fn add_private_overlay(
        &self,
        runtime: Option<tokio::runtime::Handle>,
        overlay_id: &Arc<OverlayShortId>,
        overlay_key: &Arc<KeyOption>,
        peers: &[Arc<KeyId>],
    ) -> Result<bool> {
        if self.add_overlay(runtime, overlay_id, Some(overlay_key.clone()))? {
            let shard = self
                .shards
                .get(overlay_id)
                .ok_or_else(|| error!("Cannot add the private overlay {}", overlay_id))?;
            let shard = shard.value();
            let our_key = overlay_key.id();
            for peer in peers {
                if peer == our_key {
                    continue;
                }
                shard.known_peers.put(peer.clone())?;
            }
            shard.update_neighbours(Self::MAX_SHARD_NEIGHBOURS)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Add private overlay peers
    pub fn add_private_peers(
        &self,
        local_adnl_key: &Arc<KeyId>,
        peers: Vec<(IpAddress, KeyOption)>,
    ) -> Result<Vec<Arc<KeyId>>> {
        let mut ret = Vec::new();
        for (ip, key) in peers {
            if let Some(peer) = self.adnl.add_peer(local_adnl_key, &ip, &Arc::new(key))? {
                ret.push(peer)
            }
        }
        Ok(ret)
    }

    /// Add public overlay peer
    pub fn add_public_peer(
        &self,
        peer_ip_address: &IpAddress,
        peer: &Node,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<Option<Arc<KeyId>>> {
        use dashmap::mapref::entry::Entry;

        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Trying add peer to unknown public overlay {}", overlay_id))?;
        let shard = shard.value();
        if shard.overlay_key.is_some() {
            fail!(
                "Trying to add public peer to private overlay {}",
                overlay_id
            )
        }
        if let Err(e) = OverlayUtils::verify_node(overlay_id, peer) {
            log::warn!(target: TARGET, "Error when verifying Overlay peer: {}", e);
            return Ok(None);
        }
        let ret = self.adnl.add_peer(
            self.node_key.id(),
            peer_ip_address,
            &Arc::new(KeyOption::from_tl_public_key(&peer.id)?),
        )?;
        let result = if let Some(ret) = ret {
            ret
        } else {
            return Ok(None);
        };
        shard.bad_peers.remove(&result);
        shard.known_peers.put(result.clone())?;
        if shard.random_peers.count() < Self::MAX_SHARD_PEERS {
            shard.random_peers.put(result.clone())?;
        }
        if shard.neighbours.count() < Self::MAX_SHARD_NEIGHBOURS {
            shard.neighbours.put(result.clone())?;
        }

        match shard.nodes.entry(result.clone()) {
            Entry::Vacant(entry) => {
                entry.insert(peer.clone());
            }
            Entry::Occupied(entry) => {
                if entry.get().version < peer.version {
                    entry.replace_entry(peer.clone());
                }
            }
        };

        Ok(Some(result))
    }

    /// Add shard
    pub fn add_shard(
        &self,
        runtime: Option<tokio::runtime::Handle>,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<bool> {
        self.add_overlay(runtime, overlay_id, None)
    }

    /// Broadcast message
    pub async fn broadcast(
        &self,
        overlay_id: &Arc<OverlayShortId>,
        data: &[u8],
        source: Option<&Arc<KeyOption>>,
    ) -> Result<BroadcastSendInfo> {
        log::trace!(target: TARGET, "Broadcast {} bytes", data.len());
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Trying broadcast to unknown overlay {}", overlay_id))?;
        let shard = shard.value();
        let source = source.unwrap_or(&self.node_key);
        let overlay_key = shard.overlay_key.as_ref().unwrap_or(&self.node_key).id();
        if data.len() <= Self::MAX_SIZE_ORDINARY_BROADCAST {
            OverlayShard::send_broadcast(shard, data, source, overlay_key).await
        } else {
            OverlayShard::create_fec_send_transfer(shard, data, source, overlay_key)
        }
    }

    /// Calculate overlay ID for shard
    pub fn calc_overlay_id(&self, workchain: i32, shard: i64) -> Result<OverlayId> {
        OverlayUtils::calc_overlay_id(workchain, shard, &self.zero_state_file_hash)
    }

    /// Calculate overlay short ID for shard
    pub fn calc_overlay_short_id(&self, workchain: i32, shard: i64) -> Result<Arc<OverlayShortId>> {
        OverlayUtils::calc_overlay_short_id(workchain, shard, &self.zero_state_file_hash)
    }

    /// Delete private_overlay
    pub fn delete_private_overlay(&self, overlay_id: &Arc<OverlayShortId>) -> Result<bool> {
        if let Some(shard) = self.shards.get(overlay_id) {
            shard
                .value()
                .overlay_key
                .as_ref()
                .ok_or_else(|| error!("Try to delete public overlay {}", overlay_id))?;
            self.shards.remove(overlay_id);
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// Delete private overlay peers
    pub fn delete_private_peers(
        &self,
        local_key: &Arc<KeyId>,
        peers: &[Arc<KeyId>],
    ) -> Result<bool> {
        let mut ret = false;
        for peer in peers {
            ret = self.adnl.delete_peer(local_key, peer)? || ret
        }
        Ok(ret)
    }

    /// Delete public overlay peer
    pub fn delete_public_peer(
        &self,
        peer: &Arc<KeyId>,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<bool> {
        let shard = self.shards.get(overlay_id).ok_or_else(|| {
            error!(
                "Trying to delete peer from unknown public overlay {}",
                overlay_id
            )
        })?;
        let shard = shard.value();
        if shard.overlay_key.is_some() {
            fail!(
                "Trying to delete public peer from private overlay {}",
                overlay_id
            )
        }

        if !shard.bad_peers.insert(peer.clone()) {
            return Ok(false);
        }

        if shard.random_peers.contains(peer) {
            shard.update_random_peers(Self::MAX_SHARD_PEERS)?
        }

        // DO NOT DELETE from ADNL, because it may be shared between overlays
        // self.adnl.delete_peer(self.node_key.id(), peer)
        Ok(true)
    }

    /// Get debug trace
    pub fn get_debug_trace(&self, overlay_id: &Arc<OverlayShortId>) -> Result<u32> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Getting trace from unknown overlay {}", overlay_id))?;
        Ok(shard.value().debug_trace.load(Ordering::Acquire))
    }

    /// Get locally cached random peers
    pub fn get_cached_random_peers(
        &self,
        dst: &AddressCache,
        overlay_id: &Arc<OverlayShortId>,
        n: u32,
    ) -> Result<()> {
        let shard = self.shards.get(overlay_id).ok_or_else(|| {
            error!(
                "Getting cached random peers from unknown overlay {}",
                overlay_id
            )
        })?;
        let shard = shard.value();
        shard.known_peers.random_set(dst, Some(&shard.bad_peers), n)
    }

    /// Get query prefix
    pub fn get_query_prefix(&self, overlay_id: &Arc<OverlayShortId>) -> Result<Vec<u8>> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Getting query prefix of unknown overlay {}", overlay_id))?;
        Ok(shard.value().query_prefix.clone())
    }

    /// overlay.GetRandomPeers
    pub async fn get_random_peers(
        &self,
        dst: &Arc<KeyId>,
        overlay_id: &Arc<OverlayShortId>,
        timeout: Option<u64>,
    ) -> Result<Option<Vec<Node>>> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Getting random peers from unknown overlay {}", overlay_id))?;
        log::trace!(target: TARGET, "Get random peers from {}", dst);
        let peers = GetRandomPeers {
            peers: self.prepare_random_peers(shard.value())?,
        };
        let query = TLObject::new(peers);
        let answer = self.query(dst, &query, overlay_id, timeout).await?;
        if let Some(answer) = answer {
            let answer: NodesBoxed = Query::parse(answer, &query)?;
            log::trace!(target: TARGET, "Got random peers from {}", dst);
            Ok(Some(self.process_random_peers(overlay_id, answer.only())?))
        } else {
            log::warn!(target: TARGET, "No random peers from {}", dst);
            Ok(None)
        }
    }

    /// Get signed node
    pub fn get_signed_node(&self, overlay_id: &Arc<OverlayShortId>) -> Result<Node> {
        self.sign_local_node(overlay_id)
    }

    /// Send message via ADNL
    pub async fn message(
        &self,
        dst: &Arc<KeyId>,
        data: &[u8],
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<()> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Sending ADNL message to unknown overlay {}", overlay_id))?;
        let shard = shard.value();
        let src = shard.overlay_key.as_ref().unwrap_or(&self.node_key).id();
        let peers = AdnlPeers::with_keys(src.clone(), dst.clone());

        let mut buf = shard.message_prefix.clone();
        buf.extend_from_slice(data);
        self.adnl.send_custom(&buf, &peers).await
    }

    /// Send query via ADNL
    pub async fn query(
        &self,
        dst: &Arc<KeyId>,
        query: &TLObject,
        overlay_id: &Arc<OverlayShortId>,
        timeout: Option<u64>,
    ) -> Result<Option<TLObject>> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Sending ADNL query to unknown overlay {}", overlay_id))?;
        let shard = shard.value();
        let src = shard.overlay_key.as_ref().unwrap_or(&self.node_key).id();
        let peers = AdnlPeers::with_keys(src.clone(), dst.clone());

        self.adnl
            .query_with_prefix(Some(&shard.query_prefix), query, &peers, timeout)
            .await
    }

    /// Send query via RLDP
    pub async fn query_via_rldp(
        &self,
        rldp: &Arc<RldpNode>,
        dst: &Arc<KeyId>,
        data: &[u8],
        max_answer_size: Option<i64>,
        roundtrip: Option<u64>,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<(Option<Vec<u8>>, u64)> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Sending RLDP query to unknown overlay {}", overlay_id))?;
        let src = shard
            .value()
            .overlay_key
            .as_ref()
            .unwrap_or(&self.node_key)
            .id();
        let peers = AdnlPeers::with_keys(src.clone(), dst.clone());

        rldp.query(data, max_answer_size, &peers, roundtrip).await
    }

    /// Wait for broadcast
    pub async fn wait_for_broadcast(
        &self,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<BroadcastRecvInfo> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Waiting for broadcast in unknown overlay {}", overlay_id))?;
        shard.value().received_rawbytes.pop().await
    }

    /// Wait for catchain
    pub async fn wait_for_catchain(
        &self,
        overlay_id: &Arc<OverlayShortId>,
    ) -> Result<(CatchainBlockUpdate, ValidatorSessionBlockUpdate, Arc<KeyId>)> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Waiting for catchain in unknown overlay {}", overlay_id))?;
        shard
            .value()
            .received_catchain
            .as_ref()
            .ok_or_else(|| error!("Waiting for catchain in public overlay {}", overlay_id))?
            .pop()
            .await
    }

    /// Wait for peers
    pub async fn wait_for_peers(&self, overlay_id: &Arc<OverlayShortId>) -> Result<Vec<Node>> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Waiting for peers in unknown overlay {}", overlay_id))?;
        shard.value().received_peers.pop().await
    }

    fn add_overlay(
        &self,
        runtime: Option<tokio::runtime::Handle>,
        overlay_id: &Arc<OverlayShortId>,
        overlay_key: Option<Arc<KeyOption>>,
    ) -> Result<bool> {
        use dashmap::mapref::entry::Entry;

        log::debug!(target: TARGET, "Add overlay {} to node", overlay_id);

        Ok(match self.shards.entry(overlay_id.clone()) {
            Entry::Vacant(entry) => {
                let message_prefix = OverlayMessage {
                    overlay: ton::int256(*overlay_id.data()),
                }
                .into_boxed();
                let query_prefix = OverlayQuery {
                    overlay: ton::int256(*overlay_id.data()),
                };
                let received_catchain = if overlay_key.is_some() {
                    let received_catchain = Arc::new(BroadcastReceiver {
                        data: lockfree::queue::Queue::new(),
                        subscribers: lockfree::queue::Queue::new(),
                        synclock: AtomicU32::new(0),
                    });
                    Some(received_catchain)
                } else {
                    None
                };

                let shard = Arc::new(OverlayShard {
                    adnl: self.adnl.clone(),
                    bad_peers: DashSet::new(),
                    known_peers: AddressCache::with_limit(Self::MAX_PEERS),
                    message_prefix: serialize(&message_prefix)?,
                    neighbours: AddressCache::with_limit(Self::MAX_SHARD_NEIGHBOURS),
                    nodes: DashMap::new(),
                    overlay_id: overlay_id.clone(),
                    overlay_key,
                    owned_broadcasts: DashMap::new(),
                    purge_broadcasts: lockfree::queue::Queue::new(),
                    purge_broadcasts_count: AtomicU32::new(0),
                    query_prefix: serialize(&query_prefix)?,
                    random_peers: AddressCache::with_limit(Self::MAX_SHARD_PEERS),
                    received_catchain,
                    received_peers: Arc::new(BroadcastReceiver {
                        data: lockfree::queue::Queue::new(),
                        subscribers: lockfree::queue::Queue::new(),
                        synclock: AtomicU32::new(0),
                    }),
                    received_rawbytes: Arc::new(BroadcastReceiver {
                        data: lockfree::queue::Queue::new(),
                        subscribers: lockfree::queue::Queue::new(),
                        synclock: AtomicU32::new(0),
                    }),
                    debug_trace: AtomicU32::new(0),
                });
                shard.update_neighbours(Self::MAX_SHARD_NEIGHBOURS)?;
                entry.insert(shard.clone());

                let handle = runtime.unwrap_or_else(tokio::runtime::Handle::current);
                handle.spawn(async move {
                    let mut timeout_peers = 0;
                    while Arc::strong_count(&shard) > 1 {
                        let upto = Self::MAX_BROADCAST_LOG;
                        while shard.purge_broadcasts_count.load(Ordering::Acquire) > upto {
                            if let Some(bcast_id) = shard.purge_broadcasts.pop() {
                                shard.owned_broadcasts.remove(&bcast_id);
                            }
                            shard.purge_broadcasts_count.fetch_sub(1, Ordering::Release);
                        }
                        timeout_peers += Self::TIMEOUT_GC;
                        if timeout_peers > Self::TIMEOUT_PEERS {
                            let result = if shard.overlay_key.is_some() {
                                shard.update_neighbours(1)
                            } else {
                                shard.update_random_peers(1)
                            };
                            if let Err(e) = result {
                                log::error!(target: TARGET, "Error: {}", e)
                            }
                            timeout_peers = 0;
                        }
                        tokio::time::sleep(Duration::from_millis(Self::TIMEOUT_GC)).await;
                    }
                });

                true
            }
            Entry::Occupied(_) => false,
        })
    }

    fn prepare_random_peers(&self, shard: &OverlayShard) -> Result<Nodes> {
        let mut ret = vec![self.sign_local_node(&shard.overlay_id)?];
        let nodes = AddressCache::with_limit(Self::MAX_RANDOM_PEERS);
        shard
            .random_peers
            .random_set(&nodes, None, Self::MAX_RANDOM_PEERS)?;
        let (mut iter, mut current) = nodes.first();
        while let Some(node) = current {
            if let Some(node) = shard.nodes.get(&node) {
                ret.push(node.value().clone())
            }
            current = nodes.next(&mut iter)
        }
        let ret = Nodes { nodes: ret.into() };
        Ok(ret)
    }

    fn process_random_peers(
        &self,
        overlay_id: &Arc<OverlayShortId>,
        peers: Nodes,
    ) -> Result<Vec<Node>> {
        let mut ret = Vec::new();
        log::trace!(target: TARGET, "-------- Got random peers:");
        let mut peers = peers.nodes.0;
        while let Some(peer) = peers.pop() {
            if self.node_key.id().data() == KeyOption::from_tl_public_key(&peer.id)?.id().data() {
                continue;
            }
            log::trace!(target: TARGET, "{:?}", peer);
            if let Err(e) = OverlayUtils::verify_node(overlay_id, &peer) {
                log::warn!(target: TARGET, "Error when verifying Overlay peer: {}", e);
                continue;
            }
            ret.push(peer)
        }
        Ok(ret)
    }

    fn process_get_random_peers(
        &self,
        shard: &OverlayShard,
        query: GetRandomPeers,
    ) -> Result<Nodes> {
        log::trace!(target: TARGET, "Got random peers request");
        let peers = self.process_random_peers(&shard.overlay_id, query.peers)?;
        BroadcastReceiver::push(&shard.received_peers, peers);
        self.prepare_random_peers(shard)
    }

    fn sign_local_node(&self, overlay_id: &Arc<OverlayShortId>) -> Result<Node> {
        let shard = self
            .shards
            .get(overlay_id)
            .ok_or_else(|| error!("Signing local node for unknown overlay {}", overlay_id))?;
        let key = shard.value().overlay_key.as_ref().unwrap_or(&self.node_key);
        let version = now();
        let local_node = NodeToSign {
            id: AdnlShortId {
                id: ton::int256(*key.id().data()),
            },
            overlay: ton::int256(*overlay_id.data()),
            version,
        }
        .into_boxed();
        let local_node = Node {
            id: key.as_tl_public_key()?,
            overlay: ton::int256(*overlay_id.data()),
            signature: ton::bytes(key.sign(&serialize(&local_node)?)?.to_vec()),
            version,
        };
        Ok(local_node)
    }
}

#[async_trait::async_trait]
impl Subscriber for OverlayNode {
    async fn try_consume_custom(&self, data: &[u8], peers: &AdnlPeers) -> Result<bool> {
        let mut bundle = deserialize_bundle(data)?;
        if (bundle.len() < 2) || (bundle.len() > 3) {
            return Ok(false);
        }
        let overlay_id = match bundle.remove(0).downcast::<OverlayMessageBoxed>() {
            Ok(msg) => {
                let OverlayMessage {
                    overlay: ton::int256(overlay_id),
                } = msg.only();
                OverlayShortId::from_data(overlay_id)
            }
            Err(msg) => {
                log::debug!(target: TARGET, "Unsupported overlay message {:?}", msg);
                return Ok(false);
            }
        };
        let overlay_shard = if let Some(overlay_shard) = self.shards.get(&overlay_id) {
            overlay_shard
        } else {
            fail!("Message to unknown overlay {}", overlay_id)
        };

        if bundle.len() == 2 {
            // Private overlay
            let catchain_update = match bundle.remove(0).downcast::<CatchainBlockUpdateBoxed>() {
                Ok(CatchainBlockUpdateBoxed::Catchain_BlockUpdate(upd)) => *upd,
                Err(msg) => fail!("Unsupported private overlay message {:?}", msg),
            };
            let validator_session_update = match bundle
                .remove(0)
                .downcast::<ValidatorSessionBlockUpdateBoxed>()
            {
                Ok(ValidatorSessionBlockUpdateBoxed::ValidatorSession_BlockUpdate(upd)) => *upd,
                Err(msg) => fail!("Unsupported private overlay message {:?}", msg),
            };
            let receiver = overlay_shard
                .value()
                .received_catchain
                .as_ref()
                .ok_or_else(|| error!("No catchain receiver in private overlay {}", overlay_id))?;
            BroadcastReceiver::push(
                receiver,
                (
                    catchain_update,
                    validator_session_update,
                    peers.other().clone(),
                ),
            );
            Ok(true)
        } else {
            // Public overlay
            match bundle.remove(0).downcast::<Broadcast>() {
                Ok(Broadcast::Overlay_BroadcastFec(bcast)) => {
                    OverlayShard::receive_fec_broadcast(overlay_shard.value(), bcast, data, &peers)
                        .await?;
                    Ok(true)
                }
                Ok(Broadcast::Overlay_Broadcast(bcast)) => {
                    OverlayShard::receive_broadcast(overlay_shard.value(), bcast, data, &peers)
                        .await?;
                    Ok(true)
                }
                Ok(bcast) => fail!("Unsupported overlay broadcast message {:?}", bcast),
                Err(msg) => fail!("Unsupported overlay message {:?}", msg),
            }
        }
    }

    async fn try_consume_query(&self, object: TLObject, peers: &AdnlPeers) -> Result<QueryResult> {
        log::warn!(
            target: TARGET,
            "try_consume_query OVERLAY {:?} from {}",
            object,
            peers.other()
        );
        Ok(QueryResult::Rejected(object))
    }

    async fn try_consume_query_bundle(
        &self,
        mut objects: Vec<TLObject>,
        peers: &AdnlPeers,
    ) -> Result<QueryResult> {
        if objects.len() != 2 {
            return Ok(QueryResult::RejectedBundle(objects));
        }
        let overlay_id = match objects.remove(0).downcast::<OverlayQuery>() {
            Ok(query) => {
                let ton::int256(overlay_id) = query.overlay;
                OverlayShortId::from_data(overlay_id)
            }
            Err(query) => {
                objects.insert(0, query);
                return Ok(QueryResult::RejectedBundle(objects));
            }
        };

        let object = match objects.remove(0).downcast::<GetRandomPeers>() {
            Ok(query) => {
                let overlay_shard = if let Some(overlay_shard) = self.shards.get(&overlay_id) {
                    overlay_shard
                } else {
                    fail!("Query to unknown overlay {}", overlay_id)
                };
                return QueryResult::consume(
                    self.process_get_random_peers(overlay_shard.value(), query)?,
                );
            }
            Err(object) => object,
        };
        let consumer = if let Some(consumer) = self.consumers.get(&overlay_id) {
            consumer
        } else {
            fail!("No consumer for message in overlay {}", overlay_id)
        };
        match consumer.value().try_consume_query(object, peers).await {
            Err(msg) => fail!("Unsupported query, overlay: {}, query: {}", overlay_id, msg),
            r => r,
        }
    }
}
