/- Bridges `OrdinalAnalysis.IDn.AxiomsPA`'s abstract induction-axiom theorem (proved against a
`Ω_n · 2`-height convention built from the *natural* sum `nadd`, `OmegaTwo_pa := nadd (Omega
(n - 1)) (Omega (n - 1))`, since it is a faithful per-level lift of `ID1.AxiomsPA`'s Cantor-
normal-form bookkeeping) into `OrdinalAnalysis.IDn.Embed`'s `EmbedHyps.induction_axiom` field
(stated against the self-contained `AxDerivable`/`OmegaTwo := Omega (n-1) + Omega (n-1)`, the *ordinary*
sum, per `Embed.lean`'s header: `IDn.Rank` is additive, so `Embed.lean` needs no `omegaMul`/`nadd`
at all).

**The bridging inequality** (`OmegaTwo_pa_le_OmegaTwo`): `OmegaTwo_pa (n := n) ≤ OmegaTwo (n :=
n)`. This is *not* the general fact "`nadd a b ≥ a + b`" run backwards (that inequality goes the
wrong way for arbitrary `a`, `b`): it holds here because, term by term,

  `nadd (Omega (n-1)) (Omega (n-1))`
    `= Omega (n-1) + Omega (n-1)`       -- `nadd a a = a + a` when `a`'s own CNF entry list is a
                                            *singleton* (`entries (Omega n) = [Omega n]`, a
                                            consequence of `Omega n` being a fixed point of
                                            `omegaPow`): merging `[Omega n]` with itself and
                                            ordinally adding `[Omega n]` to itself both produce the
                                            two-element list `[Omega n, Omega n]`, since neither
                                            merge-reordering nor add's left-truncation-by-`<`ever
                                            triggers between two *equal* entries.

Composing with `ThetaWNoteD.add_ofNat_eq_nadd` (`a + ofNat m = nadd a (ofNat m)`, `AxiomsPA.lean`,
unconditional in `a`) turns this into the height bound `axDerivable_of_le_of_pa` needs:
`nadd (OmegaTwo_pa (n := n)) (ofNat m) ≤ OmegaTwo (n := n) + ofNat m`.

**The `k : Fin n` gap** (found, not silently patched around): `AxiomsPA.induction_axiom` is
compiled with an actual, unavoidable `(k : Fin n)` parameter — forced by its own `include k in`,
in turn forced by the internal lemmas it calls (`embK_fixitr_inst k`, `numSubst_embK_succInd k`)
needing `k` *only inside their own proofs* (their stated conclusions, checked directly, do not
mention `k` at all: e.g. `numSubst_embK_succInd`'s type is `numSubst g ▹ embK (succInd φ) =
succIndI (numSubst₁ g ▹ embK φ)`). So the mathematical content of `induction_axiom` is uniform in
`k`, but as *compiled* in `AxiomsPA.lean` it still demands a witness `k : Fin n`, which does not
exist when `n = 0`. `EmbedHyps.induction_axiom`'s field, by contrast, is stated for every `n`
including `0`. Fixing this at the source (dropping `include k in` from those four lemmas, since
none of their types need it) is out of scope here — `AxiomsPA.lean` is not one of this brief's
files to edit. What is needed instead, and is exactly the standing assumption already used by
every other assembled `IDn` result (`IDn/LowerBoundAux2.lean`'s `lvl0`, `IDn/Theorem.lean`'s
`idn_upper_bound`, `IDn/UpperFinal.lean`'s `idn_upper_bound'` — all take `(hn : 0 < n)`), is a
witness `k : Fin n` (equivalently `0 < n`) supplied at the point `EmbedHyps A` is *assembled*;
`embedHyps_induction_of_pa` below takes it as an explicit parameter for that reason, one level
before the field itself, rather than leaving it as a silent `sorry`-shaped hole. -/
import OrdinalAnalysis.IDn.AxiomsPA
import OrdinalAnalysis.IDn.Embed

set_option autoImplicit false

namespace OrdinalAnalysis

namespace ThetaWNoteD

open ThetaWTerm in
/-- `Ω_j + Ω_j = Ω_j ⊕ Ω_j`: `Omega j`'s own CNF entry list is the singleton `[Omega j]`
(`entries_Omega`), so both the merge (`nadd`) and the ordinal sum (`+`) of `Omega j` with itself
produce the same two-element list `[Omega j, Omega j]` — merging two equal singletons needs no
reordering, and adding does not truncate an entry equal to (only strictly below) the other side's
leading exponent. -/
theorem Omega_add_self_eq_nadd_self (j : ℕ) :
    ThetaWNoteD.Omega j + ThetaWNoteD.Omega j =
      ThetaWNoteD.nadd (ThetaWNoteD.Omega j) (ThetaWNoteD.Omega j) := by
  apply ThetaWNoteD.ext_entries
  rw [ThetaWNoteD.entries_add, ThetaWNoteD.entries_nadd, ThetaWNoteD.entries_Omega,
    addL_cons, mergeL_cons_cons_of_le [] [] (le_refl' _)]
  simp [geb]

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-- **The height-convention bridge**: `AxiomsPA`'s `Ω_n · 2` (built from the natural sum, over
`Omega (n - 1)`) is below `Embed`'s `Ω_n · 2` (built from the ordinary sum, over `Omega n`). -/
theorem OmegaTwo_pa_le_OmegaTwo (n : ℕ) :
    OmegaTwo_pa (n := n) ≤ OmegaTwo (n := n) := by
  -- both are `Ω_n · 2` over `Omega (n - 1)`; `+` and `⊕` coincide on `Ω ⊕ Ω`
  calc OmegaTwo_pa (n := n)
      = ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.Omega (n - 1)) := rfl
    _ = ThetaWNoteD.Omega (n - 1) + ThetaWNoteD.Omega (n - 1) :=
        (ThetaWNoteD.Omega_add_self_eq_nadd_self (n - 1)).symm
    _ ≤ OmegaTwo (n := n) := le_rfl

/-- **`AxDerivableOfLeHyp` for the real `Embed.AxDerivable`**: instantiates `AxiomsPA`'s abstract
`axDerivable_of_le` hypothesis at `Embed`'s genuine, self-contained `AxDerivable`/`axDerivable_of_le`
pair, bridging the two height conventions via `OmegaTwo_pa_le_OmegaTwo`. -/
theorem axDerivable_of_le_of_pa : AxDerivableOfLeHyp A AxDerivable :=
  fun {σ} m β hβ hder =>
    axDerivable_of_le A m β
      (le_trans hβ (by
        rw [ThetaWNoteD.add_ofNat_eq_nadd]
        exact ThetaWNoteD.nadd_le_nadd_left' _ (OmegaTwo_pa_le_OmegaTwo n)))
      hder

/-- **The bridge lemma**: `EmbedHyps.induction_axiom`'s field, discharged from `AxiomsPA.
induction_axiom` plus the genuine `Embed.AxDerivable`/`axDerivable_of_le`. Takes an explicit
`k : Fin n` beyond the field's own hypotheses — see the file header for exactly why
`AxiomsPA.induction_axiom` needs one (a `k`-independent fact, forced to carry a `k : Fin n`
witness by how it is compiled) and why this is not a loss of strength for the project's actual
use (every assembled `IDn` result already assumes `0 < n`). -/
theorem embedHyps_induction_of_pa (k : Fin n) (taut : TautHyp A) (Sim : SimRel n)
    (sim_subst_closed : SimSubstClosedHyp n Sim) (replace_head : ReplaceHeadHyp n A Sim)
    (allClosure_derivable : AllClosureDerivableHyp A) :
    (∀ j, XFreeL (A j)) → ∀ {σ : Sentence (LXIn n)},
      σ ∈ InductionScheme (LXIn n) Set.univ → AxDerivable A σ :=
  fun hA {σ} h =>
    induction_axiom k AxDerivable taut Sim sim_subst_closed replace_head
      axDerivable_of_le_of_pa allClosure_derivable hA h

end IDn

end OrdinalAnalysis
