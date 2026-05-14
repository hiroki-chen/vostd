use core::marker::PointeeSized;
use vstd::prelude::*;

verus! {

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(AsRefSpec via AsRefSpecImpl)]
pub trait ExAsRef<T: PointeeSized>: PointeeSized {
    type ExternalTraitSpecificationFor: core::convert::AsRef<T>;

    // Note that this returns a reference not `T` commonly found
    // in Verus code. This is because the trait does not ensure
    // that `T` is `Sized`, and thus dereferncing the pointer to
    // `T` and then invoking `eq` is not possible.
    //
    // A straightforward implemnentation for this spec is to return
    // a reference to the `view` of the type.
    spec fn as_ref_spec(&self) -> &T;

    fn as_ref(&self) -> (ret: &T)
        ensures
            self.as_ref_spec() == ret,
    ;
}

} // verus!
