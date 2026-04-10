type Slot = usize;

// invariant: bijective & total (every missing key is the identity).
// Thus the key & value sets are equal, we call them the support.
// Every identity pairs are missing in v. v is sorted by keys.
struct SlotMap {
    v: Vec<(Slot, Slot)>
}
