/- Source: OrdinalAnalysis\IDn\EmbedHypsLogic.lean (level `k : Fin n` generalised to `k : ℕ`, ID_n -> ID_omega). -/

import OrdinalAnalysis.IDw.Embed
import OrdinalAnalysis.IDw.AxiomsLogic
/-
  Bridge lemmas from `IDw/AxiomsLogic.lean` (`_al` suffix: `AxDerivable_al`, height convention
  `OmegaTwo_al := nadd OmegaW OmegaW`) to `IDw/Embed.lean`'s `EmbedHyps` structure
  (`AxDerivable`, height convention `OmegaTwo := OmegaW + OmegaW`, ordinary `+`). The two
  files were written independently, but with genuinely different height notations for what is
  mathematically the same quantity `Ω_ω · 2`; this file reconciles them field by field.

  **What reconciles by monotonicity alone (`eq_axiom`, `paMinus_axiom`).** Both
  `AxDerivable`/`AxDerivable_al` are `∃ m, ∀ H nice, IDwDerivable A zero H (height + ofNat m)
  [emb (embK σ)]`, so `AxDerivable_al A σ → AxDerivable A σ` reduces to a single inequality
  `nadd OmegaTwo_al (ofNat m) ≤ OmegaTwo + ofNat m` for every `m`
  (`nadd_omegaTwo_al_ofNat_le`), which is exactly `IDwDerivable.mono_height`'s hypothesis.
  This inequality is proved from two facts, neither needing an inequality in the *other*
  direction:

  * `OmegaTwo_al ≤ OmegaTwo`: in fact equality, since both are built over `OmegaW`:
    `nadd OmegaW OmegaW = OmegaW + OmegaW` by the next point.
  * `Ω + Ω = nadd Ω Ω` for a principal `Ω` — more generally,
    **the ordinal sum and the natural sum of `a` and `b` coincide whenever every entry of `a`
    dominates every entry of `b`** (`ThetaVNoteD.add_eq_nadd_of_forall_le`): both `addL` and
    `mergeL` on the two (already sorted, non-increasing) exponent lists then reduce to plain
    list concatenation, `addL` by definition (its filter keeps everything) and `mergeL` by
    induction using `mergeL_cons_cons_of_le` at every step. This is what lets `Ω_ω + Ω_ω`
    (Embed's convention) and `Ω_ω ⊕ Ω_ω` (AxiomsLogic's convention) — and, applied a second time,
    `(Ω_ω ⊕ Ω_ω) + ofNat m` and `nadd (Ω_ω ⊕ Ω_ω) (ofNat m)` — be identified, since `OmegaW`'s
    own entries list is the singleton `[ThetaVTerm.OmegaW]` (reflexivity supplies the
    domination) and `ofNat m`'s entries are `m` copies of the strictly smaller unit term
    (`ThetaVTerm.nil_lt_prin`).

  **`taut`.** `EmbedHyps.taut` is at height `omegaMul (rk ψ)` (the additive version is refuted,
  `IDw/TautAdditive.lean`), which is exactly `IDw.AxiomsLogic.taut`, and `IDw.taut` needs no
  boundedness hypothesis on `A`: `embedHyps_taut_of_al` is a restatement.

  **Not covered.** `induction_axiom` (`AxiomsPA`), `closure_axiom`/`indAx_axiom`
  (`AxiomsIDCases`), the remaining fields of `EmbedHyps`, are not `AxiomsLogic` content.

  Contents.

    `ThetaVNoteD.add_eq_nadd_of_forall_le`   the general `+`/`⊕` coincidence fact
    `omegaTwo_al_le_omegaTwo`, `nadd_omegaTwo_al_ofNat_le`
    `axDerivable_of_al`                      `AxDerivable_al A σ → AxDerivable A σ`
    `embedHyps_taut_of_al`                   the `taut` field
    `EmbedHypsLogicPart`, `embedHypsLogicPart`   the two axiom fields (`eq_axiom`, `paMinus_axiom`)
-/

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### The ordinal sum and the natural sum coincide under one-sided domination -/

namespace ThetaVNoteD

open ThetaVTerm

private theorem filter_geb_eq_self :
    ∀ {xs : List ThetaVTerm} {y : ThetaVTerm}, (∀ x ∈ xs, y ≤ x) →
      xs.filter (fun x => geb x y) = xs
  | [], _, _ => rfl
  | x :: xs, y, h => by
      rw [List.filter_cons_of_pos (by simp [geb, h x List.mem_cons_self]),
        filter_geb_eq_self (fun x' hx' => h x' (List.mem_cons_of_mem _ hx'))]

private theorem addL_eq_append_of_forall_ge_head {xs : List ThetaVTerm} {y : ThetaVTerm}
    (ys : List ThetaVTerm) (h : ∀ x ∈ xs, y ≤ x) : addL xs (y :: ys) = xs ++ y :: ys := by
  rw [addL_cons, filter_geb_eq_self h]

private theorem mergeL_eq_append_of_forall_le :
    ∀ (xs ys : List ThetaVTerm), (∀ x ∈ xs, ∀ y ∈ ys, y ≤ x) → mergeL xs ys = xs ++ ys
  | [], ys, _ => by rw [mergeL_nil_left, List.nil_append]
  | x :: xs, [], _ => by rw [mergeL_nil_right, List.append_nil]
  | x :: xs, y :: ys, h => by
      have hyx : y ≤ x := h x List.mem_cons_self y List.mem_cons_self
      rw [mergeL_cons_cons_of_le xs ys hyx,
        mergeL_eq_append_of_forall_le xs (y :: ys)
          (fun x' hx' y' hy' => h x' (List.mem_cons_of_mem _ hx') y' hy'),
        List.cons_append]

private theorem addL_eq_mergeL_of_forall_le :
    ∀ (xs ys : List ThetaVTerm), (∀ x ∈ xs, ∀ y ∈ ys, y ≤ x) → addL xs ys = mergeL xs ys
  | xs, [], _ => by rw [addL_nil, mergeL_nil_right]
  | xs, y :: ys, h => by
      rw [addL_eq_append_of_forall_ge_head ys (fun x hx => h x hx y List.mem_cons_self),
        mergeL_eq_append_of_forall_le xs (y :: ys) h]

/-- **The ordinal sum `a + b` and the natural sum `nadd a b` coincide whenever every entry of
`a` dominates every entry of `b`**: both reduce to plain concatenation of the two (already
sorted, non-increasing) exponent lists. General-purpose addition to `Ordinal/ThetaW/Arith.lean`'s
API, needed here because `IDw/Embed.lean` and `IDw/AxiomsLogic.lean` state the same height
(`Ω_n · 2`, `Ω_n · 2 + m`) using `+` and `nadd` respectively. -/
theorem add_eq_nadd_of_forall_le {a b : ThetaVNoteD}
    (h : ∀ x ∈ a.entries, ∀ y ∈ b.entries, y ≤ x) : a + b = nadd a b := by
  apply ext_entries
  rw [entries_add, entries_nadd, addL_eq_mergeL_of_forall_le a.entries b.entries h]

-- `nadd_le_nadd_left` lives in `Ordinal/ThetaV/Arith.lean` (single copy).

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

variable {A : Semisentence LForm 2}

/-! ### `OmegaTwo_al ≤ OmegaTwo`, and the shifted version with `ofNat m` -/

private theorem entries_OmegaW_el : ThetaVNoteD.OmegaW.entries = [ThetaVTerm.OmegaW] := rfl

/-- Every entry of `OmegaW + OmegaW`'s exponent list is `OmegaW` itself (via `mem_addL` on
`entries_add`, without computing the two-element list explicitly). -/
private theorem mem_omega_add_omega_entries {x : ThetaVTerm}
    (hx : x ∈ (ThetaVNoteD.OmegaW + ThetaVNoteD.OmegaW).entries) : x = ThetaVTerm.OmegaW := by
  rw [ThetaVNoteD.entries_add] at hx
  rcases ThetaVTerm.mem_addL hx with hx | hx <;>
    · rw [entries_OmegaW_el, List.mem_singleton] at hx
      exact hx

theorem omegaTwo_al_le_omegaTwo : OmegaTwo_al ≤ OmegaTwo := by
  -- both are `Ω_ω · 2` over `OmegaW`; `+` and `⊕` coincide on `Ω ⊕ Ω`
  have hdom : ∀ x ∈ ThetaVNoteD.OmegaW.entries,
      ∀ y ∈ ThetaVNoteD.OmegaW.entries, y ≤ x := by
    intro x hx y hy
    rw [entries_OmegaW_el, List.mem_singleton] at hx hy
    rw [hx, hy]
  have h3 : ThetaVNoteD.nadd ThetaVNoteD.OmegaW ThetaVNoteD.OmegaW = OmegaTwo :=
    (ThetaVNoteD.add_eq_nadd_of_forall_le hdom).symm
  exact le_of_eq h3

/-- **The key inequality**: `AxiomsLogic`'s height `Ω_ω · 2 ⊕ m` (`OmegaTwo_al`, `nadd`) is
below `Embed`'s height `Ω_ω · 2 + m` (`OmegaTwo + ofNat m`, ordinary `+`), for the *same* `m` — no
shift is needed on the `ofNat` part, since `OmegaTwo`'s exponent list is entirely made of copies
of `OmegaW`, which dominates `ofNat m`'s unit entries (`ThetaVTerm.nil_lt_prin`), so `+` and
`nadd` coincide there too (`add_eq_nadd_of_forall_le`). -/
theorem nadd_omegaTwo_al_ofNat_le (m : ℕ) :
    ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m) ≤ OmegaTwo + ThetaVNoteD.ofNat m := by
  have hmono : ThetaVNoteD.nadd OmegaTwo_al (ThetaVNoteD.ofNat m) ≤
      ThetaVNoteD.nadd OmegaTwo (ThetaVNoteD.ofNat m) :=
    ThetaVNoteD.nadd_le_nadd_left _ omegaTwo_al_le_omegaTwo
  have hdom : ∀ x ∈ OmegaTwo.entries, ∀ y ∈ (ThetaVNoteD.ofNat m).entries, y ≤ x := by
    intro x hx y hy
    have hxeq : x = ThetaVTerm.OmegaW := mem_omega_add_omega_entries hx
    rw [ThetaVNoteD.entries_ofNat] at hy
    have hyeq : y = ThetaVTerm.sum [] := List.eq_of_mem_replicate hy
    rw [hxeq, hyeq]
    exact le_of_lt (ThetaVTerm.nil_lt_prin ThetaVTerm.isPrin_OmegaW)
  have heq : ThetaVNoteD.nadd OmegaTwo (ThetaVNoteD.ofNat m) = OmegaTwo + ThetaVNoteD.ofNat m :=
    (ThetaVNoteD.add_eq_nadd_of_forall_le hdom).symm
  exact heq ▸ hmono

/-! ### `AxDerivable_al A σ → AxDerivable A σ`, and the two covered `EmbedHyps` fields -/

/-- **`AxDerivable_al` implies `AxDerivable`**: the two are the same existential statement up to
the height inequality `nadd_omegaTwo_al_ofNat_le`, discharged by `IDwDerivable.mono_height`
inside `axDerivable_of_le` (`IDw/Embed.lean`), reusing the *same* witness `m`. -/
theorem axDerivable_of_al {σ : Sentence (LXJ)} (h : AxDerivable_al A σ) : AxDerivable A σ := by
  obtain ⟨m, hm⟩ := h
  exact axDerivable_of_le A m _ (nadd_omegaTwo_al_ofNat_le m) hm

/-- The equality axioms, bridged from `IDw.AxiomsLogic.eq_axiom`. -/
theorem embedHyps_eq_axiom_of_al {σ : Sentence (LXJ)}
    (h : σ ∈ 𝗘𝗤 (LXJ)) : AxDerivable A σ :=
  axDerivable_of_al (eq_axiom h)

/-- The `𝗣𝗔⁻` axioms, bridged from `IDw.AxiomsLogic.paMinus_axiom`. -/
theorem embedHyps_paMinus_axiom_of_al {σ : Sentence (LXJ)}
    (h : σ ∈ Theory.lMap toLXJ 𝗣𝗔⁻) : AxDerivable A σ :=
  axDerivable_of_al (paMinus_axiom h)

/-- **`EmbedHyps.taut`** (height `omegaMul (rk ψ)`) is `IDw.AxiomsLogic.taut`, verbatim: no
boundedness hypothesis on `A` is needed any more. -/
theorem embedHyps_taut_of_al {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.NiceS H)
    (ψ : Proposition LIinfW) (hc : ψ.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] :=
  taut hH ψ hc

/-- **Partial `EmbedHyps` builder**: the two axiom fields obtainable from `IDw.AxiomsLogic` by the
height monotonicity `OmegaTwo_al ≤ OmegaTwo` alone (`eq_axiom`, `paMinus_axiom`). Leaves
`induction_axiom` (`AxiomsPA`) and `closure_axiom`/`indAx_axiom` (`AxiomsIDCases`) for later
(`taut` is `embedHyps_taut_of_al`). -/
structure EmbedHypsLogicPart (A : Semisentence LForm 2) : Prop where
  eq_axiom : ∀ {σ : Sentence (LXJ)}, σ ∈ 𝗘𝗤 (LXJ) → AxDerivable A σ
  paMinus_axiom : ∀ {σ : Sentence (LXJ)}, σ ∈ Theory.lMap toLXJ 𝗣𝗔⁻ → AxDerivable A σ

theorem embedHypsLogicPart : EmbedHypsLogicPart A where
  eq_axiom h := embedHyps_eq_axiom_of_al h
  paMinus_axiom h := embedHyps_paMinus_axiom_of_al h

end IDw

end OrdinalAnalysis
