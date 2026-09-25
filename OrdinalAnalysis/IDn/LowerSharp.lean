/-
  The sharp lower bound for `IDn n (WForms orderFormulas n)`: transfinite induction up to the
  Buchholz–Pohlers ordinal `c n = ϑ₀(ϑ_n 0)` itself, meeting the sharp upper bound
  `Upper.idn_upper_bound'` (which already reaches every `a ≺ c n`) exactly at `c n`.

  `IDn/LowerBound.lean`'s `idn_lower_bound` only refutes `TI_{Omega 0}` (`Omega 0 = Ω₁`), far
  above `c n` (`ThetaWNoteD.c n < ThetaWNoteD.Omega 0`, `ThetaWTerm.cTerm_lt_Omega0`). Closing
  the gap needs re-running `LowerBound.lean`'s diagonal argument at the bound `a := c n` instead
  of `a := Omega 0`; the only place `a` enters that argument is the single inequality `b.1 < a`
  (`not_derivable_fieldInI0`'s `hb1`), used once, to certify `code b.1 ≺ ⌜a⌝` so that `x := code
  b.1` qualifies for `fieldInI0 F n hn a`'s own defining quantifier. So the sharp bound follows
  from *exactly* `LowerBound.lean`'s hypotheses, provided the stage `b` `CollapseCorollary`
  hands back is *itself* known to satisfy the sharper `b.1 < c n` (not merely `b.1 < Omega 0`).

  **`CollapseCorollarySharp`, the one further hypothesis.** `Collapsing.Theorem.
  collapse_zero_bound` — already a fully proved theorem, no hypothesis beyond `CollapseHyps`
  — produces `b` of the *exact* shape `b.1 = Collapsing.psi k (ω^{μ̄_m + μ̄_m + α})` for whatever
  `m ≤ n` and height `α` the (not yet composed) cut-rank bridging from the embedding's raw
  output feeds it (`LowerBound.lean`'s own header: the multi-level collapsing corollary,
  Buchholz Theorem 4.8 §2.4, "is not written yet"). `Ordinal/ThetaW/TowerCofinal.lean`'s
  `theta0_hat_lt_c` — the tower-cofinality fact an earlier pass searched for
  and did not find — shows this shape is *always* `< c n`, given only that `μ̄_m ≺ ϑ_n(0)`
  (true for every `m ≤ n`, `muBar_lt_thetaZero` below) and that `α ≺ ϑ_n(0)` with no level-`0`
  subterm of its own (`E_0(α) = ∅`; plausible for the heights this chain produces — built from
  `Omega`/`one`/`ofNat`/`+` at levels `≥ 1` only, e.g. the visible raw height `OmegaTwo (n:=n) +
  ofNat r` of `CollapseCorollary`'s own hypothesis clause already has both properties, being
  literally `Omega n + Omega n + ofNat r` — but *verifying* that the height surviving the actual
  (unwritten) elimination/predicative-cut chain still has them is part of the same unwritten
  bridging, not re-derived here). `CollapseCorollarySharp` is stated in exactly the shape this
  reasoning produces (`CollapseCorollary`'s own hypothesis clause, unchanged; only the bound in
  the conclusion strengthened from `Omega (lvl0 hn).val` to `ThetaWNoteD.c n`), so that closing
  the shared gap is again a drop-in, not a restatement — exactly `CollapseCorollary`'s own
  design principle (see `LowerBound.lean`'s header), one bound sharper.

  Contents.

    `muBar_lt_thetaZero`         `μ̄_m ≺ ϑ_n(0)` for every `m ≤ n` (`n ≥ 1`)
    `muBar_Ehull_eq_empty`       `E_0(μ̄_m) = ∅` for every `m`
    `CollapseCorollarySharp`     the one open link, documented above
    `not_derivable_fieldInI0_sharp`   no derivation of the embedded sentence, at the bound `c n`
    `idn_lower_bound_sharp`      the lower bound at the bound `c n`
    `idn_theorem_sharp`          both halves, meeting exactly at `c n`
-/
import OrdinalAnalysis.IDn.Theorem2
import OrdinalAnalysis.Ordinal.ThetaW.TowerCofinal

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDn

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.IDn.Upper
open OrdinalAnalysis.IDn.Internal (code)

variable {n : ℕ}

/-! ### `μ̄_m ≺ ϑ_n(0)`, for every `m ≤ n` -/

/-- `Ω_s ≺ ϑ_n(0)` for `s ≤ n - 1`, packaged for `muBar`'s two cases. -/
theorem Omega_add_one_lt_thetaZero_of_le {s k : ℕ} (h : s ≤ k) :
    ThetaWNoteD.Omega s + ThetaWNoteD.one < ThetaWNoteD.thetaZero k := by
  rcases h.lt_or_eq with h' | rfl
  · have h1 : ThetaWNoteD.Omega s < ThetaWNoteD.Omega k :=
      ThetaWNoteD.lt_iff.mpr ((ThetaWTerm.Omega_lt_Omega_iff s k).mpr h')
    have h2 := ThetaWNoteD.succ_lt_prin (ThetaWNoteD.isPrin_thetaZero k)
      (lt_trans h1 (ThetaWNoteD.Omega_lt_thetaZero k))
    rwa [ThetaWNoteD.add_one_eq_succ]
  · exact ThetaWNoteD.Omega_add_one_lt_thetaZero s

/-- **`μ̄_m ≺ ϑ_n(0)` for every `m ≤ n`** (`n ≥ 1`): the base bound `theta0_hat_lt_c` needs for
`μ := Collapsing.muBar m`. -/
theorem muBar_lt_thetaZero (hn : 0 < n) {m : ℕ} (hm : m ≤ n) :
    Collapsing.muBar m < ThetaWNoteD.thetaZero (n - 1) := by
  cases m with
  | zero =>
      rw [Collapsing.muBar_zero]
      exact lt_trans (ThetaWNoteD.zero_lt_Omega (n - 1)) (ThetaWNoteD.Omega_lt_thetaZero (n - 1))
  | succ s =>
      rw [Collapsing.muBar_succ]
      exact Omega_add_one_lt_thetaZero_of_le (by omega)

/-- **`E_0(μ̄_m) = ∅`** for every `m`: `muBar m` is built from `Omega`/`one` only, no `ϑ`-subterm
at all. -/
theorem muBar_Ehull_eq_empty (m : ℕ) : ThetaWNoteD.Ehull 0 (Collapsing.muBar m) = ∅ := by
  cases m with
  | zero => rw [Collapsing.muBar_zero]; exact ThetaWNoteD.Ehull_zero_hull 0
  | succ s => rw [Collapsing.muBar_succ]; exact ThetaWNoteD.Ehull_Omega_add_one_hull 0 s

/-! ### The notation lemma, instantiated at `collapse_zero_bound`'s own output shape -/

/-- **`psi0_hat_lt_c`, the notation lemma proved at the exact shape
`Collapsing.Theorem.collapse_zero_bound` produces**: for `m ≤ n` and any height `α ≺ ϑ_n(0)`
with no level-`0` subterm of its own (`E_0(α) = ∅`), `ψ_0(α̂) = ϑ_0(ω^{μ̄_m+μ̄_m+α}) ≺ c_n`.
`Collapsing.psi`/`Collapsing.hat` are total (junk `zero` outside the domain `DomK 0 _`), so no
`HullHypGe`/domain hypothesis is needed here at all: off the domain the left side is `zero ≺
c_n` trivially (`c_n` is principal, hence positive); on the domain it unfolds to
`ThetaWNoteD.theta0_hat_lt_c`. -/
theorem psi0_hat_lt_c (hn : 0 < n) {m : ℕ} (hm : m ≤ n) {α : ThetaWNoteD}
    (hα : α < ThetaWNoteD.thetaZero (n - 1)) (hαE : ThetaWNoteD.Ehull 0 α = ∅) :
    Collapsing.psi (lvl0 hn).val (Collapsing.hat ThetaWNoteD.zero (Collapsing.muBar m) α) <
      ThetaWNoteD.c n := by
  show Collapsing.psi 0 (Collapsing.hat ThetaWNoteD.zero (Collapsing.muBar m) α) < ThetaWNoteD.c n
  rw [Collapsing.hat_zero]
  show Notn.ThetaWNoteD.thetaD 0
      (ThetaWNoteD.omegaPow (Collapsing.muBar m + Collapsing.muBar m + α)) < ThetaWNoteD.c n
  by_cases hdom : Notn.ThetaWNoteD.DomK 0
      (ThetaWNoteD.omegaPow (Collapsing.muBar m + Collapsing.muBar m + α))
  · refine ThetaWNoteD.lt_iff.mpr ?_
    rw [Notn.ThetaWNoteD.thetaD_of_dom hdom]
    exact ThetaWNoteD.theta0_hat_lt_c hn (muBar_lt_thetaZero hn hm) hα (muBar_Ehull_eq_empty m) hαE
  · refine ThetaWNoteD.lt_iff.mpr ?_
    rw [Notn.ThetaWNoteD.thetaD_of_not_dom hdom]
    exact ThetaWTerm.nil_lt_prin trivial

/-! ### The one open link, sharpened -/

/-- **The multi-level collapsing corollary, at the sharp bound `c n`.** See the file header for
exactly why this is the natural strengthening of `LowerBound.lean`'s `CollapseCorollary`
(same hypothesis clause; the conclusion's bound sharpened from `Omega (lvl0 hn).val` to
`ThetaWNoteD.c n`, justified by `theta0_hat_lt_c` once the shared cut-rank bridging gap is
closed). -/
def CollapseCorollarySharp (hn : 0 < n) : Prop :=
  ∀ {m r : ℕ} {φ : Proposition (LIinfN n)}, SigmaW (lvl0 hn) φ →
    (∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable (WForms orderFormulas n) (OmegaPlus (n := n) m) H
        (OmegaTwo (n := n) + ThetaWNoteD.ofNat r) [φ]) →
    ∃ (b : StageAt (lvl0 hn).val) (H : Set ThetaWNoteD → Set ThetaWNoteD),
      ThetaWNoteD.NiceS H ∧ b.1 < ThetaWNoteD.c n ∧
      IDnDerivable (WForms orderFormulas n) b.1 H b.1 (Collapsing.capSeq (lvl0 hn) b [φ])

/-! ### No derivation of the embedded sentence, at the bound `c n` -/

/-- **No derivation of the embedded `fieldInI0`, at the bound `c n`**, given
`CollapseCorollarySharp`: the exact analogue of `LowerBound.lean`'s `not_derivable_fieldInI0`,
with `ThetaWNoteD.Omega 0` replaced by `ThetaWNoteD.c n` throughout — the only place the bound
enters the argument is the single inequality `hb1`, used once to certify `code b.1 ≺ ⌜c n⌝`. -/
theorem not_derivable_fieldInI0_sharp (hn : 0 < n) (hcol : CollapseCorollarySharp hn) {m r : ℕ}
    (d : ∀ H : Set ThetaWNoteD → Set ThetaWNoteD, ThetaWNoteD.NiceS H →
      IDnDerivable (WForms orderFormulas n) (OmegaPlus (n := n) m) H
        (OmegaTwo (n := n) + ThetaWNoteD.ofNat r)
        [embed (fieldInI0 orderFormulas n hn (ThetaWNoteD.c n) : Proposition (LXIn n))]) :
    False := by
  obtain ⟨b, _, _, hbc, D⟩ := hcol (sigmaW_embed_fieldInI0 orderFormulas hn (ThetaWNoteD.c n)) d
  rw [Collapsing.capSeq_singleton] at D
  obtain ⟨φ, hφ, htrue⟩ :=
    StageSem.sound (fun _ => True) (WForms orderFormulas n) (wForms_levelBounded orderFormulas n)
      D (lt_trans hbc (ThetaWTerm.cTerm_lt_Omega0 n))
  rw [List.mem_singleton.mp hφ] at htrue
  unfold StageSem.TrueSN at htrue
  rw [capAt_embed, Semiformula.eval_lMap, StageSem.lMap_stageHom_stageStrucN,
    Semiformula.eval_emb, eval_fieldInI0_stdIN] at htrue
  have hb1 : b.1 < ThetaWNoteD.c n := hbc
  have hmem : (code b.1.1 : ℕ) ∈
      StageSem.stageEnvAt (StageSem.stageSetN (fun _ => True) (WForms orderFormulas n))
        (lvl0 hn) b (lvl0 hn) := by
    refine htrue (code b.1.1 : ℕ) ⟨(Internal.eval_fld_iff b.1.1).mpr b.1.2,
      (Internal.eval_fld_iff (ThetaWNoteD.c n).1).mpr (ThetaWNoteD.c n).2, ?_⟩
    exact (Internal.eval_lt_iff_lt b.1.1 (ThetaWNoteD.c n).1).mpr hb1
  rw [StageSem.stageEnvAt, dif_pos rfl] at hmem
  have := (codeAt0_mem_stageSetN_iff hn (fun _ => True) b b.1).mp hmem
  exact lt_irrefl b.1 this

/-! ### The sharp lower bound -/

/-- **`IDn n (WForms orderFormulas n) ⊬ TI_{c n}(≺, X)`**, given `EmbedHyps` and
`CollapseCorollarySharp`: the sharp companion of `LowerBound.lean`'s `idn_lower_bound`, meeting
`Upper.idn_upper_bound'` exactly at `c n`. -/
theorem idn_lower_bound_sharp (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n))
    (hcol : CollapseCorollarySharp hn) :
    ¬ IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) := by
  intro h
  have hσ := provable_fieldInI0_of_ti orderFormulas hn h
  obtain ⟨m, r, hmr⟩ := embedding_theorem_xfree hyps (wForms_positive orderFormulas n)
    (xFreeL_WForms orderFormulas) (xFreeL_fieldInI0 orderFormulas hn (ThetaWNoteD.c n)) hσ
  exact not_derivable_fieldInI0_sharp hn hcol hmr

/-! ### Both halves, meeting exactly at `c n` -/

/-- **The Buchholz–Pohlers analysis of `ID_n`, sharp**: `ID_n` proves transfinite induction up
to every notation `a ≺ c_n` (hypothesis-free, `Upper.idn_upper_bound'`), and does not prove it
at `c_n` itself, given `EmbedHyps` and `CollapseCorollarySharp`. Unlike `Theorem2.lean`'s
`idn_theorem` (whose two halves meet at `Omega 0`, not `c_n`), the two halves here meet exactly
at the sharp Buchholz–Pohlers ordinal. -/
theorem idn_theorem_sharp (hn : 0 < n) (hyps : EmbedHyps (WForms orderFormulas n))
    (hcol : CollapseCorollarySharp hn) :
    (∀ a : ThetaWNoteD, a < ThetaWNoteD.c n →
        IDn n (WForms orderFormulas n) ⊢ tiUptoSentence orderFormulas (Fin n) a) ∧
      ¬ IDn n (WForms orderFormulas n) ⊢
        tiUptoSentence orderFormulas (Fin n) (ThetaWNoteD.c n) := by
  refine ⟨fun a ha => ?_, idn_lower_bound_sharp hn hyps hcol⟩
  rw [orderFormulas_eq_codedOrderFacts]
  exact idn_upper_bound' n hn a ha

end IDn

end OrdinalAnalysis
