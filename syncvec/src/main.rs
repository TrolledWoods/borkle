use syncvec::SyncVec;

fn main() {
    use std::sync::Arc;
    use std::thread;

    let sync_vec = Arc::new(SyncVec::<u64>::new());

    let mut handles = Vec::new();
    let total = (1+2+3+4+5+6) * 50;
    for _ in 0..50 {
        let sync_vec = sync_vec.clone();
        handles.push(thread::spawn(move || {
            sync_vec.push(1);
            sync_vec.push(2);
            sync_vec.push(3);
            sync_vec.push(4);
            sync_vec.push(5);
            sync_vec.push(6);
        }));
    }

    for handle in handles {
        handle.join().unwrap();
    }

    let summed = sync_vec.iter().copied().sum::<u64>();
    assert_eq!(summed, total);
}
