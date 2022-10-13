mod implementation {

    pub type Clock = u32;
    pub fn merge_clocks(a: Clock, b: Clock) -> Clock {
        a.max(b)
    }

    const N: usize = 8;
    pub type VectorClock = [Clock; N];
    pub fn merge_vc(a: VectorClock, b: VectorClock) -> VectorClock {
        let mut out = [0; N];
        for i in 0..N {
            out[i] = merge_clocks(a[i], b[i]);
        }
        out
    }
}

#[cfg(crux)]
mod crux_commutativity {
    use super::implementation::*;
    extern crate crucible;
    use crucible::*;
    extern crate crucible_spec_macro;
    use crucible_spec_macro::crux_spec_for;
    // Prove commutativity
    #[crux_spec_for(merge_clocks)]
    fn merge_clocks_commutative() {
        let a = <Clock>::symbolic("a");
        let b = <Clock>::symbolic("b");
        let ab = merge_clocks(a, b);
        crucible_assert!(ab == merge_clocks(b, a));
    }
    #[crux_test]
    fn merge_vc_commutative() {
        // merge_clocks_commutative_spec().enable(); // FIXME: this breaks the proof
        let a = <VectorClock>::symbolic("a");
        let b = <VectorClock>::symbolic("b");
        let ab = merge_vc(a, b);
        let ba = merge_vc(b, a);
        crucible_assert!(ab == ba);
    }
}

mod cryptol_spec {
    use super::implementation::*;
    extern crate crucible;
    use crucible::cryptol;
    // Spec for vc merge functions
    cryptol! {
        path "Unused"; // This "path <string>;" thing is required even though we don't use external specs
        pub fn merge_clocks(a:Clock,b:Clock) -> Clock
            = r#"\(a:[32]) (b:[32]) ->
                    if a > b then a else b"#;
        pub fn merge_vc(a: VectorClock, b: VectorClock) -> VectorClock
            = r#"\(as:[8][32]) (bs:[8][32]) ->
                    [ if a > b then a else b
                        | a <- as
                        | b <- bs
                    ]"#;
    }
}

#[cfg(crux)]
mod crux_spec_equivalence {
    use super::{cryptol_spec, implementation::*};
    extern crate crucible;
    use crucible::*;
    extern crate crucible_spec_macro;
    use crucible_spec_macro::crux_spec_for;
    // Prove equivalence to cryptol spec
    #[crux_spec_for(merge_clocks)]
    fn merge_c_equiv() {
        let a = <Clock>::symbolic("a");
        let b = <Clock>::symbolic("b");
        let out = merge_clocks(a, b);
        crucible_assert!(out == cryptol_spec::merge_clocks(a, b));
    }
    #[crux_spec_for(merge_vc)]
    fn merge_vc_equiv() {
        merge_c_equiv_spec().enable();
        let a = <VectorClock>::symbolic("a");
        let b = <VectorClock>::symbolic("b");
        let out = merge_vc(a, b);
        crucible_assert!(out == cryptol_spec::merge_vc(a, b));
    }
}
