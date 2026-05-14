//! Experimental: formalization of the weak memory model.
use vstd::prelude::*;
use vstd::resource::Loc;

verus! {

pub type WeakMemoryTimestamp = nat;

pub type WeakMemoryHistory<T> = Map<WeakMemoryTimestamp, WeakMemoryMessage<T>>;

pub tracked struct WeakMemoryMessage<T> {
    pub ghost value: T,
    /// The view published by a release write, if this message was created by
    /// one. Acquire reads of this message join the reader's view with it.
    pub ghost release_view: Option<WeakMemoryThreadView>,
}

/// A weak memory is a mapping from memory locations to sets of messages.
pub tracked struct WeakMemory<T> {
    pub ghost mem: Map<Loc, WeakMemoryHistory<T>>,
}

/// Each thread will have its local observations through a `[WeakMemoryThreadView]`.
/// During a read from a location `\ell`, the thread can observe _any_ message so long as
/// `M(\ell) >= V(\ell)`.
pub tracked struct WeakMemoryThreadView {
    pub ghost view: Map<Loc, WeakMemoryTimestamp>,
}

impl<T> WeakMemoryMessage<T> {
    pub open spec fn relaxed(value: T) -> Self {
        WeakMemoryMessage { value, release_view: None }
    }

    pub open spec fn release(value: T, release_view: WeakMemoryThreadView) -> Self {
        WeakMemoryMessage { value, release_view: Some(release_view) }
    }

    pub open spec fn wf(self, mem: WeakMemory<T>) -> bool {
        self.release_view is Some ==> self.release_view->0.wf(mem)
    }

    pub open spec fn has_release_view(self) -> bool {
        self.release_view is Some
    }

    pub open spec fn released_view(self) -> WeakMemoryThreadView {
        self.release_view->0
    }
}

impl<T> WeakMemory<T> {
    pub open spec fn wf(self) -> bool {
        &&& self.mem.dom().finite()
        &&& forall|loc: Loc| #[trigger] self.mem.contains_key(loc) ==> self.mem[loc].dom().finite()
        &&& forall|loc: Loc| #[trigger]
            self.mem.contains_key(loc) ==> self.mem[loc].dom().contains(0)
        &&& forall|loc: Loc, t: WeakMemoryTimestamp|
            #![trigger self.mem[loc][t]]
            self.mem.contains_key(loc) && self.mem[loc].contains_key(t) ==> self.mem[loc][t].wf(
                self,
            )
    }
}

pub open spec fn hist_wf<T>(hist: WeakMemoryHistory<T>) -> bool {
    &&& hist.dom().finite()
    &&& hist.dom().contains(0)
}

impl<T> WeakMemory<T> {
    pub open spec fn can_read(self, v: WeakMemoryThreadView, loc: Loc, t: nat) -> bool {
        &&& self.mem.contains_key(loc)
        &&& self.mem[loc].contains_key(t)
        &&& v.view.contains_key(loc)
        &&& v.view[loc] <= t
    }

    /// Obtain the message at a given location and timestamp. Requires that the message exists.
    pub open spec fn message_at(self, loc: Loc, t: WeakMemoryTimestamp) -> WeakMemoryMessage<T>
        recommends
            self.mem.contains_key(loc),
            self.mem[loc].contains_key(t)
    {
        self.mem[loc][t]
    }

    pub open spec fn can_write(self, v: WeakMemoryThreadView, loc: Loc, t: nat) -> bool {
        &&& self.wf()
        &&& v.wf(self)
        &&& self.mem.contains_key(loc)
        &&& v.view.contains_key(loc)
        &&& self.mem[loc].contains_key(t)
        &&& v.view[loc] <= t
        &&& forall|old_t: WeakMemoryTimestamp|
            #![trigger self.mem[loc].contains_key(old_t)]
            self.mem[loc].contains_key(old_t) ==> old_t <= t
    }

    pub open spec fn can_append(self, v: WeakMemoryThreadView, loc: Loc, t: nat) -> bool {
        &&& self.wf()
        &&& v.wf(self)
        &&& self.mem.contains_key(loc)
        &&& v.view.contains_key(loc)
        &&& !self.mem[loc].contains_key(t)
        &&& v.view[loc] < t
        &&& forall|old_t: WeakMemoryTimestamp|
            #![trigger self.mem[loc].contains_key(old_t)]
            self.mem[loc].contains_key(old_t) ==> old_t < t
    }

    pub open spec fn append(
        self,
        loc: Loc,
        t: WeakMemoryTimestamp,
        msg: WeakMemoryMessage<T>,
    ) -> Self
        recommends
            self.mem.contains_key(loc),
    {
        WeakMemory { mem: self.mem.insert(loc, self.mem[loc].insert(t, msg)) }
    }

    pub proof fn tracked_append(
        tracked &mut self,
        tracked view: &mut WeakMemoryThreadView,
        tracked loc: Loc,
        tracked t: nat,
        msg: WeakMemoryMessage<T>,
    )
        requires
            old(self).can_append(*old(view), loc, t),
            msg.wf(*old(self)),
        ensures
            final(self).mem == old(self).append(loc, t, msg).mem,
            final(view).view == old(view).view.insert(loc, t),
            final(self).wf(),
            final(view).wf(*final(self)),
            final(self).can_write(*final(view), loc, t),
            final(self).message_at(loc, t) == msg,
    {
        self.mem = self.mem.insert(loc, self.mem[loc].insert(t, msg));
        view.view = view.view.insert(loc, t);
    }

    pub proof fn relaxed_store_append(
        tracked &mut self,
        tracked view: &mut WeakMemoryThreadView,
        tracked loc: Loc,
        tracked t: nat,
        tracked value: T,
    )
        requires
            old(self).can_append(*old(view), loc, t),
        ensures
            final(self).mem == old(self).append(loc, t, WeakMemoryMessage::relaxed(value)).mem,
            final(view).view == old(view).view.insert(loc, t),
            final(self).wf(),
            final(view).wf(*final(self)),
            final(self).can_write(*final(view), loc, t),
            final(self).message_at(loc, t) == WeakMemoryMessage::relaxed(value),
    {
        let ghost msg = WeakMemoryMessage::relaxed(value);
        self.tracked_append(view, loc, t, msg);
    }

    pub proof fn release_store_append(
        tracked &mut self,
        tracked view: &mut WeakMemoryThreadView,
        tracked loc: Loc,
        tracked t: nat,
        tracked value: T,
    )
        requires
            old(self).can_append(*old(view), loc, t),
        ensures
            final(self).mem == old(self).append(loc, t, WeakMemoryMessage::release(value, *old(view))).mem,
            final(view).view == old(view).view.insert(loc, t),
            final(self).wf(),
            final(view).wf(*final(self)),
            final(self).can_write(*final(view), loc, t),
            final(self).message_at(loc, t) == WeakMemoryMessage::release(value, *old(view)),
    {
        let ghost msg = WeakMemoryMessage::release(value, *old(view));
        self.tracked_append(view, loc, t, msg);
    }
}

// partialord for views are:
// V1 <= V2 iff forall loc in dom(M), V1(loc) <= V2(loc)
impl WeakMemoryThreadView {
    pub open spec fn wf<T>(self, m: WeakMemory<T>) -> bool {
        &&& self.view.dom() =~= m.mem.dom()
        &&& forall|loc: Loc| #[trigger] m.mem.contains_key(loc) ==> self.view.contains_key(loc)
        &&& forall|loc: Loc| #[trigger] self.view.contains_key(loc) ==> m.mem.contains_key(loc)
    }

    pub open spec fn le<T>(self, other: Self, m: WeakMemory<T>) -> bool {
        &&& self.wf(m)
        &&& other.wf(m)
        &&& forall|loc: Loc| #[trigger]
            m.mem.contains_key(loc) ==> self.view[loc] <= other.view[loc]
    }

    pub open spec fn join<T>(self, other: Self, m: WeakMemory<T>) -> Self {
        WeakMemoryThreadView {
            view: Map::new(
                |loc: Loc| m.mem.contains_key(loc),
                |loc: Loc|
                    if self.view[loc] >= other.view[loc] {
                        self.view[loc]
                    } else {
                        other.view[loc]
                    },
            ),
        }
    }

    pub proof fn tracked_join<T>(
        tracked &mut self,
        other: WeakMemoryThreadView,
        tracked mem: &WeakMemory<T>,
    )
        requires
            old(self).wf(*mem),
            other.wf(*mem),
        ensures
            final(self).view == old(self).join(other, *mem).view,
            final(self).wf(*mem),
    {
        let ghost old_self = *old(self);
        self.view = Map::new(
            |loc: Loc| mem.mem.contains_key(loc),
            |loc: Loc|
                if old_self.view[loc] >= other.view[loc] {
                    old_self.view[loc]
                } else {
                    other.view[loc]
                },
        );
    }

    pub proof fn read_advance<T>(
        tracked &mut self,
        tracked mem: &WeakMemory<T>,
        tracked loc: Loc,
        tracked t: nat,
    )
        requires
            old(self).wf(*mem),
            mem.can_read(*old(self), loc, t),
        ensures
            final(self).wf(*mem),
            final(self).view == old(self).view.insert(loc, t),
    {
        self.view = self.view.insert(loc, t);
    }

    pub open spec fn acquire_advance<T>(
        self,
        mem: WeakMemory<T>,
        loc: Loc,
        t: WeakMemoryTimestamp,
    ) -> Self {
        let loc_view = WeakMemoryThreadView { view: self.view.insert(loc, t) };
        let msg = mem.message_at(loc, t);
        if msg.release_view is Some {
            loc_view.join(msg.release_view->0, mem)
        } else {
            loc_view
        }
    }

    pub proof fn acquire_read_advance<T>(
        tracked &mut self,
        tracked mem: &WeakMemory<T>,
        tracked loc: Loc,
        tracked t: nat,
    )
        requires
            old(self).wf(*mem),
            mem.wf(),
            mem.can_read(*old(self), loc, t),
        ensures
            final(self).wf(*mem),
            final(self).view == old(self).acquire_advance(*mem, loc, t).view,
    {
        let ghost old_self = *old(self);
        self.view = self.view.insert(loc, t);
        if mem.message_at(loc, t).release_view is Some {
            let ghost release_view = mem.message_at(loc, t).release_view->0;
            assert(mem.message_at(loc, t).wf(*mem));
            assert(release_view.wf(*mem));
            self.tracked_join(release_view, mem);
        }
        assert(self.view == old_self.acquire_advance(*mem, loc, t).view);
    }
}

} // verus!
