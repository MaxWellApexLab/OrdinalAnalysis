/-
  Bridge lemmas from `IDn/AxiomsLogic.lean` (`_al` suffix: `AxDerivable_al`, height convention
  `OmegaTwo_al := nadd (Omega (n-1)) (Omega (n-1))`) to `IDn/Embed.lean`'s `EmbedHyps` structure
  (`AxDerivable`, height convention `OmegaTwo := Omega (n-1) + Omega (n-1)`, ordinary `+`). The two
  files were written independently against the *same* `n`, but with genuinely different height
  notations for what is mathematically the same quantity `Ω_n · 2`; this file reconciles them
  field by field.

  **What reconciles by monotonicity alone (`eq_axiom`, `paMinus_axiom`).** Both
  `AxDerivable`/`AxDerivable_al` are `∃ m, ∀ H nice, IDnDerivable A zero H (height + ofNat m)
  [emb (embK σ)]`, so `AxDerivable_al A σ → AxDerivable A σ` reduces to a single inequality
  `nadd (OmegaTwo_al (n := n)) (ofNat m) ≤ OmegaTwo (n := n) + ofNat m` for every `m`
  (`nadd_omegaTwo_al_ofNat_le`), which is exactly `IDnDerivable.mono_height`'s hypothesis.
  This inequality is proved from two facts, neither needing an inequality in the *other*
  direction:

  * `OmegaTwo_al (n := n) ≤ OmegaTwo (n := n)`: in fact equality, since both are built over
    `Omega (n - 1)` (Embed's `OmegaTwo` was sharpened from `Omega n` to `Omega (n - 1)`):
    `nadd (Omega (n-1)) (Omega (n-1)) = Omega (n-1) + Omega (n-1)` by the
    next point.
  * `Omega j + Omega j = nadd (Omega j) (Omega j)` for every `j` — more generally,
    **the ordinal sum and the natural sum of `a` and `b` coincide whenever every entry of `a`
    dominates every entry of `b`** (`ThetaWNoteD.add_eq_nadd_of_forall_le`): both `addL` and
    `mergeL` on the two (already sorted, non-increasing) exponent lists then reduce to plain
    list concatenation, `addL` by definition (its filter keeps everything) and `mergeL` by
    induction using `mergeL_cons_cons_of_le` at every step. This is the general fact this file
    contributes to `Ordinal/ThetaW/Arith.lean`'s API; it is what lets `Ω_n + Ω_n` (Embed's
    convention) and `Ω_n ⊕ Ω_n` (AxiomsLogic's convention) — and, applied a second time,
    `(Ω_n ⊕ Ω_n) + ofNat m` and `nadd (Ω_n ⊕ Ω_n) (ofNat m)` — be identified, since `Omega j`'s
    own entries list is the singleton `[ThetaWTerm.Omega j]` (reflexivity supplies the
    domination) and `ofNat m`'s entries are `m` copies of the strictly smaller unit term
    (`ThetaWTerm.nil_lt_prin`).

  **What does not reconcile by monotonicity (`taut`).** `EmbedHyps.taut` needs derivability at
  height `rk ψ` (`IDn/Embed.lean`'s header: `IDn/Rank.lean` is additive, not `omegaMul`-wrapped,
  by design — this is *smaller* than `AxiomsLogic`'s `ID1`-ported Lemma 6.1, which delivers
  `omegaMul (rk ψ)` (`IDn.AxiomsLogic.taut`, ω · rk ψ, strictly larger than `rk ψ` for any
  `rk ψ ≠ 0`, since `rk ψ` is generally not additively principal — e.g. `rk` of a formula of
  positive complexity is `Omega _ + ofNat c` with `c > 0`, not a fixed point of `omegaMul`).
  `IDnDerivable.mono_height` only ever produces derivability at a *larger* height from a proof
  at a smaller one, never the reverse, so a proof at `omegaMul (rk ψ)` cannot be downgraded to
  one at `rk ψ` this way. `IDn.AxiomsLogic.taut` also needs `FamilyLevelBounded A`, which
  `EmbedHyps.taut` does not require at all. Bridging `taut` therefore needs a fresh proof of
  Freund's Lemma 6.1 under the additive height (re-running `taut_and`/`taut_all`/`taut_stage`'s
  ~300-line structural induction with `rk ψ` in place of `omegaMul (rk ψ)` throughout), which is
  left, together with `induction_axiom` (`AxiomsPA`, not yet ported to
  `IDn/`), `closure_axiom`/`indAx_axiom` (`AxiomsID`, likewise), and `replaceHeadNumI`
  (`Evaluate`), for later.

  Contents.

    `ThetaWNoteD.add_eq_nadd_of_forall_le`   the general `+`/`⊕` coincidence fact
    `omegaTwo_al_le_omegaTwo`, `nadd_omegaTwo_al_ofNat_le`
    `axDerivable_of_al`                      `AxDerivable_al A σ → AxDerivable A σ`
    `EmbedHypsLogicPart`, `embedHypsLogicPart`   the two covered fields (`eq_axiom`, `paMinus_axiom`)
-/
import OrdinalAnalysis.IDn.Embed
import OrdinalAnalysis.IDn.AxiomsLogic

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### The ordinal sum and the natural sum coincide under one-sided domination -/

namespace ThetaWNoteD

open ThetaWTerm

private theorem filter_geb_eq_self :
    ∀ {xs : List ThetaWTerm} {y : ThetaWTerm}, (∀ x ∈ xs, y ≤ x) →
      xs.filter (fun x => geb x y) = xs
  | [], _, _ => rfl
  | x :: xs, y, h => by
      rw [List.filter_cons_of_pos (by simp [geb, h x List.mem_cons_self]),
        filter_geb_eq_self (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))]

private theorem addL_eq_append_of_forall_ge_head {xs : List ThetaWTerm} {y : ThetaWTerm}
    (ys : List ThetaWTerm) (h : ∀ x ∈ xs, y ≤ x) : addL xs (y :: ys) = xs ++ y :: ys := by
  rw [addL_cons, filter_geb_eq_self h]

private theorem mergeL_eq_append_of_forall_le :
    ∀ (xs ys : List ThetaWTerm), (∀ x ∈ xs, ∀ y ∈ ys, y ≤ x) → mergeL xs ys = xs ++ ys
  | [], ys, _ => by rw [mergeL_nil_left, List.nil_append]
  | x :: xs, [], _ => by rw [mergeL_nil_right, List.append_nil]
  | x :: xs, y :: ys, h => by
      have hyx : y ≤ x := h x List.mem_cons_self y List.mem_cons_self
      rw [mergeL_cons_cons_of_le xs ys hyx,
        mergeL_eq_append_of_forall_le xs (y :: ys)
          (fun x' hx' y' hy' => h x' (List.mem_cons_of_mem _ hx') y' hy'),
        List.cons_append]

private theorem addL_eq_mergeL_of_forall_le :
    ∀ (xs ys : List ThetaWTerm), (∀ x ∈ xs, ∀ y ∈ ys, y ≤ x) → addL xs ys = mergeL xs ys
  | xs, [], _ => by rw [addL_nil, mergeL_nil_right]
  | xs, y :: ys, h => by
      rw [addL_eq_append_of_forall_ge_head ys (fun x hx => h x hx y List.mem_cons_self),
        mergeL_eq_append_of_forall_le xs (y :: ys) h]

/-- **The ordinal sum `a + b` and the natural sum `nadd a b` coincide whenever every entry of
`a` dominates every entry of `b`**: both reduce to plain concatenation of the two (already
sorted, non-increasing) exponent lists. General-purpose addition to `Ordinal/ThetaW/Arith.lean`'s
API, needed here because `IDn/Embed.lean` and `IDn/AxiomsLogic.lean` state the same height
(`Ω_n · 2`, `Ω_n · 2 + m`) using `+` and `nadd` respectively. -/
theorem add_eq_nadd_of_forall_le {a b : ThetaWNoteD}
    (h : ∀ x ∈ a.entries, ∀ y ∈ b.entries, y ≤ x) : a + b = nadd a b := by
  apply ext_entries
  rw [entries_add, entries_nadd, addL_eq_mergeL_of_forall_le a.entries b.entries h]

/-- `nadd` is monotone in its left argument (via `nadd_comm` and `nadd_le_nadd_right`; only the
right-argument version is in `Ordinal/ThetaW/Arith.lean`). -/
theorem nadd_le_nadd_left {a a' : ThetaWNoteD} (b : ThetaWNoteD) (h : a ≤ a') :
    nadd a b ≤ nadd a' b := by
  rw [nadd_comm a b, nadd_comm a' b]
  exact nadd_le_nadd_right b h

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {n : ℕ} {A : Fin n → Semisentence (LXIn n) 1}

/-! ### `OmegaTwo_al (n := n) ≤ OmegaTwo (n := n)`, and the shifted version with `ofNat m` -/

/-- Every entry of `Omega j + Omega j`'s exponent list is `Omega j` itself (via `mem_addL` on
`entries_add`, without computing the two-element list explicitly). -/
private theorem mem_omega_add_omega_entries {j : ℕ} {x : ThetaWTerm}
    (hx : x ∈ (ThetaWNoteD.Omega j + ThetaWNoteD.Omega j).entries) : x = ThetaWTerm.Omega j := by
  rw [ThetaWNoteD.entries_add] at hx
  rcases ThetaWTerm.mem_addL hx with hx | hx <;>
    · rw [ThetaWNoteD.entries_Omega, List.mem_singleton] at hx
      exact hx

theorem omegaTwo_al_le_omegaTwo (n : ℕ) : OmegaTwo_al (n := n) ≤ OmegaTwo (n := n) := by
  -- both are `Ω_n · 2` over `Omega (n - 1)`; `+` and `⊕` coincide on `Ω ⊕ Ω`
  have hdom : ∀ x ∈ (ThetaWNoteD.Omega (n - 1)).entries,
      ∀ y ∈ (ThetaWNoteD.Omega (n - 1)).entries, y ≤ x := by
    intro x hx y hy
    rw [ThetaWNoteD.entries_Omega, List.mem_singleton] at hx hy
    rw [hx, hy]
  have h3 : ThetaWNoteD.nadd (ThetaWNoteD.Omega (n - 1)) (ThetaWNoteD.Omega (n - 1)) =
      OmegaTwo (n := n) :=
    (ThetaWNoteD.add_eq_nadd_of_forall_le hdom).symm
  exact le_of_eq h3

/-- **The key inequality**: `AxiomsLogic`'s height `Ω_n · 2 ⊕ m` (`OmegaTwo_al`, `nadd`) is
below `Embed`'s height `Ω_n · 2 + m` (`OmegaTwo`, ordinary `+`), for the *same* `m` — no shift
is needed on the `ofNat` part, since `OmegaTwo (n := n)`'s exponent list is entirely made of
copies of `Omega n`, which dominates `ofNat m`'s unit entries (`ThetaWTerm.nil_lt_prin`), so `+`
and `nadd` coincide there too (`add_eq_nadd_of_forall_le`). -/
theorem nadd_omegaTwo_al_ofNat_le (n m : ℕ) :
    ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m) ≤
      OmegaTwo (n := n) + ThetaWNoteD.ofNat m := by
  have hmono : ThetaWNoteD.nadd (OmegaTwo_al (n := n)) (ThetaWNoteD.ofNat m) ≤
      ThetaWNoteD.nadd (OmegaTwo (n := n)) (ThetaWNoteD.ofNat m) :=
    ThetaWNoteD.nadd_le_nadd_left _ (omegaTwo_al_le_omegaTwo n)
  have hdom : ∀ x ∈ (OmegaTwo (n := n)).entries, ∀ y ∈ (ThetaWNoteD.ofNat m).entries, y ≤ x := by
    intro x hx y hy
    have hxeq : x = ThetaWTerm.Omega (n - 1) := mem_omega_add_omega_entries hx
    rw [ThetaWNoteD.entries_ofNat] at hy
    have hyeq : y = ThetaWTerm.sum [] := List.eq_of_mem_replicate hy
    rw [hxeq, hyeq]
    exact le_of_lt (ThetaWTerm.nil_lt_prin trivial)
  have heq : ThetaWNoteD.nadd (OmegaTwo (n := n)) (ThetaWNoteD.ofNat m) =
      OmegaTwo (n := n) + ThetaWNoteD.ofNat m :=
    (ThetaWNoteD.add_eq_nadd_of_forall_le hdom).symm
  exact heq ▸ hmono

/-! ### `AxDerivable_al A σ → AxDerivable A σ`, and the two covered `EmbedHyps` fields -/

/-- **`AxDerivable_al` implies `AxDerivable`**: the two are the same existential statement up to
the height inequality `nadd_omegaTwo_al_ofNat_le`, discharged by `IDnDerivable.mono_height`
inside `axDerivable_of_le` (`IDn/Embed.lean`), reusing the *same* witness `m`. -/
theorem axDerivable_of_al {σ : Sentence (LXIn n)} (h : AxDerivable_al A σ) : AxDerivable A σ := by
  obtain ⟨m, hm⟩ := h
  exact axDerivable_of_le A m _ (nadd_omegaTwo_al_ofNat_le n m) hm

/-- The equality axioms, bridged from `IDn.AxiomsLogic.eq_axiom`. -/
theorem embedHyps_eq_axiom_of_al (hAb : FamilyLevelBounded A) {σ : Sentence (LXIn n)}
    (h : σ ∈ 𝗘𝗤 (LXIn n)) : AxDerivable A σ :=
  axDerivable_of_al (eq_axiom hAb h)

/-- The `𝗣𝗔⁻` axioms, bridged from `IDn.AxiomsLogic.paMinus_axiom`. -/
theorem embedHyps_paMinus_axiom_of_al {σ : Sentence (LXIn n)}
    (h : σ ∈ Theory.lMap (toLXIN (Fin n)) 𝗣𝗔⁻) : AxDerivable A σ :=
  axDerivable_of_al (paMinus_axiom h)

/-- **Partial `EmbedHyps` builder**: the two fields obtainable from `IDn.AxiomsLogic` by the
height monotonicity `OmegaTwo_al ≤ OmegaTwo` alone (`eq_axiom`, `paMinus_axiom`). Leaves `taut`
(irreconcilable height convention — see file header), `induction_axiom` (`AxiomsPA`),
`closure_axiom`/`indAx_axiom` (`AxiomsID`), and `replaceHeadNumI` (`Evaluate`) for later.
Takes `FamilyLevelBounded A` explicitly, exactly as `EmbedHyps.induction_axiom`/`closure_axiom`/
`indAx_axiom` already take their own extra side hypotheses on `A` (`eq_axiom`'s literal field
in `EmbedHyps` has no such slot, so whoever assembles a full `EmbedHyps A` for a concrete `A`
with `FamilyLevelBounded A` in hand supplies `embedHypsLogicPart hAb .eq_axiom` for that field). -/
structure EmbedHypsLogicPart (A : Fin n → Semisentence (LXIn n) 1) : Prop where
  eq_axiom : ∀ {σ : Sentence (LXIn n)}, σ ∈ 𝗘𝗤 (LXIn n) → AxDerivable A σ
  paMinus_axiom : ∀ {σ : Sentence (LXIn n)}, σ ∈ Theory.lMap (toLXIN (Fin n)) 𝗣𝗔⁻ → AxDerivable A σ

theorem embedHypsLogicPart (hAb : FamilyLevelBounded A) : EmbedHypsLogicPart A where
  eq_axiom h := embedHyps_eq_axiom_of_al hAb h
  paMinus_axiom h := embedHyps_paMinus_axiom_of_al h

end IDn

end OrdinalAnalysis
