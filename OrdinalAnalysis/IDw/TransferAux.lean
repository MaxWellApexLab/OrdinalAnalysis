/-
  Lemma 6.1 (the tautology lemma) for `IDwDerivable`, the auxiliary layer of `IDw/Transfer.lean`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Lemma 6.1, as ported by `IDn/AxiomsLogic.lean`
  (`taut`), with the new atoms of `IDw`: a closed `Jlev ℓ (s,t)` and its negation are handled
  by the rules `(jlev)`/`(njlev)`, whose premise is the tautology for the *lower-level* stage
  atom `I_{val s} t` (of strictly smaller rank, `rk_IOmegaAt_lt_jlevAt`).

      `taut : H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ`,   every closed `ψ`, every nice `H`.

  The unfolding `unfoldW A k g t` of a stage atom has only the parameter `⟨k,g⟩` and only the
  atoms `I_k^{≺g}`, `Jlev k`, so no boundedness hypothesis on the form `A` is needed
  (`IDn.taut` needed `FamilyLevelBounded A`).

  Everything lives in the namespace `IDw.Transfer`, so that a later script port of
  `IDn/AxiomsLogic.lean` (`IDw/AxiomsLogic.lean`) does not collide with it.

  Contents.

    `le_omegaMul`, `succ_max_lt`, ...            height arithmetic
    `rk_mem`                                     the rank of a formula is in a nice `H(X)`
    `dlift`, `dswap`, `freeVariables_*`          structural helpers
    `taut_and`, `taut_all`, `taut_stage`,
    `taut_jlev`, `taut`                          Lemma 6.1
-/
import OrdinalAnalysis.IDw.Calculus
import OrdinalAnalysis.Ordinal.ThetaV.WellFoundedV

set_option autoImplicit false

namespace OrdinalAnalysis

namespace IDw

namespace Transfer

open LO LO.FirstOrder

/-! ### Height arithmetic -/

theorem le_omegaMul (a : ThetaVNoteD) : a ≤ ThetaVNoteD.omegaMul a := by
  induction a using WellFoundedLT.induction with
  | _ a ih =>
    by_contra h
    have hlt : ThetaVNoteD.omegaMul a < a := lt_of_not_ge h
    have h1 := ih _ hlt
    exact absurd (ThetaVNoteD.omegaMul_lt_omegaMul hlt) (not_lt_of_ge h1)

theorem nadd_ofNat_one (a : ThetaVNoteD) :
    ThetaVNoteD.nadd a (ThetaVNoteD.ofNat 1) = ThetaVNoteD.succ a := by
  rw [ThetaVNoteD.ofNat_one]; rfl

theorem succ_max_lt {p q B : ThetaVNoteD} (hp : ThetaVNoteD.succ p < B)
    (hq : ThetaVNoteD.succ q < B) : ThetaVNoteD.succ (max p q) < B := by
  rcases le_total p q with h | h
  · rw [max_eq_right h]; exact hq
  · rw [max_eq_left h]; exact hp

/-- `ω · x ⊕ p ≺ ω · (m + 1)` for `x ⪯ m`. -/
theorem omegaMul_nadd_lt_omegaMul_succ {x m : ThetaVNoteD} (h : x ≤ m) (p : ℕ) :
    ThetaVNoteD.nadd (ThetaVNoteD.omegaMul x) (ThetaVNoteD.ofNat p) <
      ThetaVNoteD.omegaMul (ThetaVNoteD.succ m) :=
  ThetaVNoteD.omegaMul_nadd_ofNat_lt (lt_of_le_of_lt h (ThetaVNoteD.lt_succ m)) p

/-- `γ + 1 ≺ ω · ω · δ` for `γ ≺ δ`: the stage weight in Lemma 6.1. -/
theorem succ_lt_omegaMul_omegaMul {g a : ThetaVNoteD} (h : g < a) :
    ThetaVNoteD.succ g < ThetaVNoteD.omegaMul (ThetaVNoteD.omegaMul a) := by
  have h1 : ThetaVNoteD.succ g ≤ ThetaVNoteD.succ (ThetaVNoteD.omegaMul g) :=
    ThetaVNoteD.succ_le_succ (le_omegaMul g)
  have h2 : ThetaVNoteD.succ (ThetaVNoteD.omegaMul g) < ThetaVNoteD.omegaMul a := by
    rw [← nadd_ofNat_one]; exact ThetaVNoteD.omegaMul_nadd_ofNat_lt h 1
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 (le_omegaMul _))

theorem succ_omegaMul_lt {x y : ThetaVNoteD} (h : x < y) :
    ThetaVNoteD.succ (ThetaVNoteD.omegaMul x) < ThetaVNoteD.omegaMul y := by
  rw [← nadd_ofNat_one]; exact ThetaVNoteD.omegaMul_nadd_ofNat_lt h 1

theorem lt_nadd_ofNat_succ (a : ThetaVNoteD) (p : ℕ) :
    a < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaVNoteD.lt_succ a) (by
    rw [← nadd_ofNat_one]
    exact ThetaVNoteD.nadd_le_nadd_right a (ThetaVNoteD.ofNat_le_ofNat (by omega)))

theorem ofNat_lt_nadd_ofNat_succ (a : ThetaVNoteD) (p : ℕ) :
    ThetaVNoteD.ofNat p < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat (p + 1)) :=
  lt_of_lt_of_le (ThetaVNoteD.ofNat_lt_ofNat (Nat.lt_succ_self p)) (ThetaVNoteD.le_nadd_right _ _)

theorem nadd_ofNat_lt_nadd_ofNat' (a : ThetaVNoteD) {j p : ℕ} (h : j < p) :
    ThetaVNoteD.nadd a (ThetaVNoteD.ofNat j) < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat p) :=
  ThetaVNoteD.nadd_lt_nadd_right a (ThetaVNoteD.ofNat_lt_ofNat h)

theorem ofNat_nadd_ofNat (p : ℕ) :
    ∀ q : ℕ, ThetaVNoteD.nadd (ThetaVNoteD.ofNat p) (ThetaVNoteD.ofNat q) =
      ThetaVNoteD.ofNat (p + q)
  | 0 => by rw [ThetaVNoteD.ofNat_zero, ThetaVNoteD.nadd_zero, Nat.add_zero]
  | q + 1 => by
    rw [ThetaVNoteD.ofNat_succ, ThetaVNoteD.succ, ← ThetaVNoteD.nadd_assoc,
      ofNat_nadd_ofNat p q, ← ThetaVNoteD.succ, ← ThetaVNoteD.ofNat_succ]; rfl

theorem nadd_nadd_ofNat (a : ThetaVNoteD) (i j : ℕ) :
    ThetaVNoteD.nadd (ThetaVNoteD.nadd a (ThetaVNoteD.ofNat i)) (ThetaVNoteD.ofNat j) =
      ThetaVNoteD.nadd a (ThetaVNoteD.ofNat (i + j)) := by
  rw [ThetaVNoteD.nadd_assoc, ofNat_nadd_ofNat]

theorem one_lt_nadd_ofNat_two (a : ThetaVNoteD) :
    ThetaVNoteD.one < ThetaVNoteD.nadd a (ThetaVNoteD.ofNat 2) := by
  rw [← ThetaVNoteD.ofNat_one]; exact ofNat_lt_nadd_ofNat_succ a 1

/-! ### The rank of a formula lies in a nice operator's hull -/

section RankMemSection

variable {ξ : Type*}

/-- **`rk φ ∈ H(X)`** once every stage parameter of `φ` is in `H(X)` (`Jlev` atoms and
arithmetic never obstruct: `Ω_k + 1`, `Ω_ω`, `0` lie in every nice hull). One-line
consequence of `NiceS.rk_mem'` (`IDw/CalculusAux.lean`). -/
theorem rk_mem {K : Set ThetaVNoteD → Set ThetaVNoteD} (hK : ThetaVNoteD.NiceS K)
    {X : Set ThetaVNoteD} {m : ℕ} {φ : Semiformula LIinfW ξ m}
    (h : ∀ s ∈ params φ, s.val ∈ K X) : rk φ ∈ K X :=
  hK.rk_mem' h

end RankMemSection

/-! ### Structural helpers -/

section Helpers

variable {A : Semisentence LForm 2} {ρ : ThetaVNoteD}

/-- Case analysis on a proposition of `LIinfW`, in connective form. -/
theorem cases0 {C : Proposition LIinfW → Prop}
    (hverum : C ⊤) (hfalsum : C ⊥)
    (hrel : ∀ (k : ℕ) (r : LIinfW.Rel k) (v : Fin k → SyntacticTerm LIinfW),
      C (Semiformula.rel r v))
    (hnrel : ∀ (k : ℕ) (r : LIinfW.Rel k) (v : Fin k → SyntacticTerm LIinfW),
      C (Semiformula.nrel r v))
    (hand : ∀ φ ψ : Proposition LIinfW, C (φ ⋏ ψ))
    (hor : ∀ φ ψ : Proposition LIinfW, C (φ ⋎ ψ))
    (hall : ∀ φ : Semiproposition LIinfW 1, C (∀¹ φ))
    (hexs : ∀ φ : Semiproposition LIinfW 1, C (∃¹ φ)) :
    ∀ φ : Proposition LIinfW, C φ
  | Semiformula.verum => hverum
  | Semiformula.falsum => hfalsum
  | Semiformula.rel r v => hrel _ r v
  | Semiformula.nrel r v => hnrel _ r v
  | Semiformula.and φ ψ => hand φ ψ
  | Semiformula.or φ ψ => hor φ ψ
  | Semiformula.all φ => hall φ
  | Semiformula.exs φ => hexs φ

/-- Moving a derivation to a larger operator and a larger sequent. -/
theorem dlift {K K' : Set ThetaVNoteD → Set ThetaVNoteD} {h : ThetaVNoteD}
    {Δ Δ' : Sequent LIinfW} {A : Semisentence LForm 2} {ρ : ThetaVNoteD}
    (d : IDwDerivable A ρ K h Δ) (hK' : ThetaVNoteD.IsOperator K')
    (hKK : ∀ X, K X ⊆ K' X) (hsub : Δ ⊆ Δ') (hP : paramsVal Δ' ⊆ K' ∅) :
    IDwDerivable A ρ K' h Δ' :=
  (d.mono_op hKK).weaken_seq hK' hsub hP

theorem adjoin_le_adjoin {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {Z Z' : Set ThetaVNoteD} (h : Z ⊆ Z') (X : Set ThetaVNoteD) :
    ThetaVNoteD.adjoin H Z X ⊆ ThetaVNoteD.adjoin H Z' X :=
  hH.mono (Set.union_subset_union_left X h)

theorem subset_adjoin_empty {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    (Z : Set ThetaVNoteD) : Z ⊆ ThetaVNoteD.adjoin H Z ∅ := by
  intro x hx
  exact hH.subset _ (Or.inl hx)

theorem freeVariables_subst_numI (φ : Semiformula LIinfW ℕ 1) (hφ : φ.freeVariables = ∅)
    (p : ℕ) : (φ/[numI p]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![numI p]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![numI p]) #i : SyntacticTerm LIinfW).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, numI_freeVariables] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

theorem freeVariables_subst_of_closed (φ : Semiformula LIinfW ℕ 1) (hφ : φ.freeVariables = ∅)
    {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) : (φ/[t]).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t]) (φ := φ) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · have hi' : x ∈ ((Rew.subst ![t]) #i : SyntacticTerm LIinfW).freeVariables := hi
    cases i using Fin.cases with
    | zero => simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
              exact Finset.notMem_empty x hi'
    | succ i => exact i.elim0
  · have hz' : z ∈ φ.freeVariables := hz
    rw [hφ] at hz'
    exact Finset.notMem_empty z hz'

/-- The sequent `ψ, ¬ψ` read backwards. -/
theorem dswap {H : Set ThetaVNoteD → Set ThetaVNoteD} (hH : ThetaVNoteD.IsOperator H)
    {h : ThetaVNoteD} {ψ : Proposition LIinfW} (d : IDwDerivable A ρ H h [∼ψ, ψ]) :
    IDwDerivable A ρ H h [ψ, ∼ψ] := by
  refine d.weaken_seq (Γ' := [ψ, ∼ψ]) hH (by
    intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
  have := d.params_subset
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty] at this ⊢
  exact this

theorem freeVariables_rel_arg {m k : ℕ} {r : LIinfW.Rel k}
    {v : Fin k → Semiterm LIinfW ℕ m} (h : (Semiformula.rel r v).freeVariables = ∅)
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.rel r v).freeVariables := by
    rw [Semiformula.freeVariables_rel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

theorem freeVariables_nrel_arg {m k : ℕ} {r : LIinfW.Rel k}
    {v : Fin k → Semiterm LIinfW ℕ m} (h : (Semiformula.nrel r v).freeVariables = ∅)
    (i : Fin k) : (v i).freeVariables = ∅ := by
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  have : x ∈ (Semiformula.nrel r v).freeVariables := by
    rw [Semiformula.freeVariables_nrel]
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩
  rw [h] at this
  exact Finset.notMem_empty x this

/-- A unary negated atom is `nrel r ![v 0]`. -/
theorem nrel_eq_vec {ξ : Type*} {k : ℕ} (r : LIinfW.Rel 1) (v : Fin 1 → Semiterm LIinfW ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0] := by
  congr 1; funext i; obtain rfl := Subsingleton.elim i 0; rfl

/-- A binary negated atom is `nrel r ![v 0, v 1]`. -/
theorem nrel_eq_vec2 {ξ : Type*} {k : ℕ} (r : LIinfW.Rel 2) (v : Fin 2 → Semiterm LIinfW ξ k) :
    Semiformula.nrel r v = Semiformula.nrel r ![v 0, v 1] := by
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

theorem freeVariables_rel_closed {k : ℕ} (r : LIinfW.Rel k) (v : Fin k → SyntacticTerm LIinfW)
    (hv : ∀ i, (v i).freeVariables = ∅) : (Semiformula.rel r v).freeVariables = ∅ := by
  rw [Semiformula.freeVariables_rel]
  ext x
  simp [hv]

/-- `I_k t` with `t` closed is closed. -/
theorem freeVariables_IOmegaAt {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) (k : ℕ) :
    (IOmegaAt k t).freeVariables = ∅ := by
  unfold IOmegaAt stageAt
  refine freeVariables_rel_closed _ _ fun i => ?_
  obtain rfl := Subsingleton.elim i 0
  exact ht

/-- **The unfolding of a closed term is closed.** -/
theorem freeVariables_unfold {A : Semisentence LForm 2} (k : ℕ) (a : StageAt k)
    {t : SyntacticTerm LIinfW} (ht : t.freeVariables = ∅) :
    (unfoldW A k a t).freeVariables = ∅ := by
  unfold unfoldW
  ext x
  simp only [Finset.notMem_empty, iff_false]
  intro hx
  rcases Semiformula.fvar?_rew (ω := Rew.subst ![t, Semiterm.numeral k])
    (φ := (Rewriting.emb (formAtW A k a) : Semiformula LIinfW ℕ 2)) (x := x) hx with
    ⟨i, hi⟩ | ⟨z, hz, -⟩
  · cases i using Fin.cases with
    | zero =>
      have hi' : x ∈ ((Rew.subst ![t, Semiterm.numeral k] : Rew LIinfW ℕ 2 ℕ 0) #0 :
          SyntacticTerm LIinfW).freeVariables := hi
      simp only [Rew.subst_bvar, Matrix.cons_val_zero, ht] at hi'
      exact Finset.notMem_empty x hi'
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        have hi' : x ∈ ((Rew.subst ![t, Semiterm.numeral k] : Rew LIinfW ℕ 2 ℕ 0) #1 :
            SyntacticTerm LIinfW).freeVariables := hi
        simp only [Rew.subst_bvar, Matrix.cons_val_one, Matrix.cons_val_zero,
          numeral_freeVariables] at hi'
        exact Finset.notMem_empty x hi'
      | succ i => exact i.elim0
  · have hz' : z ∈ (Rewriting.emb (formAtW A k a) : Semiformula LIinfW ℕ 2).freeVariables := hz
    rw [Semiformula.freeVariables_emb] at hz'
    exact Finset.notMem_empty z hz'

end Helpers

/-! ### Lemma 6.1 -/

section Taut

variable {A : Semisentence LForm 2} {H : Set ThetaVNoteD → Set ThetaVNoteD}

theorem params_sub_adjoin (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition LIinfW} :
    paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
  simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, Set.union_self]
  exact subset_adjoin_empty hH _

/-- Membership in `H(k(ψ))`, pointwise: the form `NiceS.rk_mem` wants. -/
theorem mem_adjoin_params (hH : ThetaVNoteD.IsOperator H) {ψ : Proposition LIinfW}
    {s : Stage} (hs : s ∈ params ψ) : s.val ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
  subset_adjoin_empty hH _ ⟨s, hs, rfl⟩

/-- **Lemma 6.1, conjunction.** -/
theorem taut_and (hH : ThetaVNoteD.NiceS H) {φ₀ φ₁ : Proposition LIinfW}
    (ih₀ : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ₀))
      (ThetaVNoteD.omegaMul (rk φ₀)) [φ₀, ∼φ₀])
    (ih₁ : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ₁))
      (ThetaVNoteD.omegaMul (rk φ₁)) [φ₁, ∼φ₁]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (φ₀ ⋏ φ₁)))
      (ThetaVNoteD.omegaMul (rk (φ₀ ⋏ φ₁))) [φ₀ ⋏ φ₁, ∼(φ₀ ⋏ φ₁)] := by
  set ψ : Proposition LIinfW := φ₀ ⋏ φ₁ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.1
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.1 _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.1
  have hneg : ∼ψ = ∼φ₀ ⋎ ∼φ₁ := by simp [hψ]
  have hrk : rk ψ = ThetaVNoteD.succ (max (rk φ₀) (rk φ₁)) := rk_and φ₀ φ₁
  have hs0 : params φ₀ ⊆ params ψ := Set.subset_union_left
  have hs1 : params φ₁ ⊆ params ψ := Set.subset_union_right
  have hs0' : Stage.val '' params φ₀ ⊆ Stage.val '' params ψ := Set.image_mono hs0
  have hs1' : Stage.val '' params φ₁ ⊆ Stage.val '' params ψ := Set.image_mono hs1
  -- the heights
  have hm0 : ThetaVNoteD.omegaMul (rk φ₀) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 (hs0 hs)))
  have hm1 : ThetaVNoteD.omegaMul (rk φ₁) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 (hs1 hs)))
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 hs))
  have hP : ∀ φ : Proposition LIinfW, params φ ⊆ params ψ →
      paramsVal [∼φ, φ, ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ)
      (Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ))
  have hP' : ∀ φ : Proposition LIinfW, params φ ⊆ params ψ →
      paramsVal [φ, ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    intro φ hφ
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
    exact Set.union_subset ((Set.image_mono hφ).trans hZ) (Set.union_subset hZ hZ)
  have d0 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ₀)) [∼φ₀, φ₀, ψ, ∼ψ] :=
    dlift ih₀ hKo (adjoin_le_adjoin hH.1 hs0')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₀ hs0)
  have d1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ₁)) [∼φ₁, φ₁, ψ, ∼ψ] :=
    dlift ih₁ hKo (adjoin_le_adjoin hH.1 hs1')
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) (hP φ₁ hs1)
  have e0 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ₀)) (ThetaVNoteD.ofNat 2)) [φ₀, ψ, ∼ψ] :=
    .orL (hK.nadd_mem hm0 (hK.ofNat_mem 2)) (hP' φ₀ hs0)
      (by rw [← hneg]; simp) (lt_nadd_ofNat_succ _ 1) d0
  have e1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ₁)) (ThetaVNoteD.ofNat 2)) [φ₁, ψ, ∼ψ] :=
    .orR (hK.nadd_mem hm1 (hK.ofNat_mem 2)) (hP' φ₁ hs1)
      (by rw [← hneg]; simp) (one_lt_nadd_ofNat_two _)
      (lt_nadd_ofNat_succ _ 1) d1
  refine .and hmψ hΓ List.mem_cons_self ?_ ?_ e0 e1
  · rw [hrk]; exact omegaMul_nadd_lt_omegaMul_succ (le_max_left _ _) 2
  · rw [hrk]; exact omegaMul_nadd_lt_omegaMul_succ (le_max_right _ _) 2

/-- **Lemma 6.1, universal quantifier.** -/
theorem taut_all (hH : ThetaVNoteD.NiceS H) {φ : Semiproposition LIinfW 1}
    (ih : ∀ p : ℕ, IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (φ/[numI p])))
      (ThetaVNoteD.omegaMul (rk (φ/[numI p]))) [φ/[numI p], ∼(φ/[numI p])]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (∀¹ φ)))
      (ThetaVNoteD.omegaMul (rk (∀¹ φ))) [∀¹ φ, ∼(∀¹ φ)] := by
  set ψ : Proposition LIinfW := ∀¹ φ with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hKo := hK.1
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.1 _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.1
  have hneg : ∼ψ = ∃¹ (∼φ) := by simp [hψ]
  have hrk : rk ψ = ThetaVNoteD.succ (rk φ) := rk_all φ
  have hsp : ∀ p, params (φ/[numI p]) = params ψ := fun p => params_subst1 φ _
  have hmφ : ThetaVNoteD.omegaMul (rk φ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1
      (show s ∈ params φ from hs)))
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 hs))
  refine .all (fun p => ThetaVNoteD.nadd (ThetaVNoteD.omegaMul (rk φ)) (ThetaVNoteD.ofNat (p + 1)))
    hmψ hΓ (φ := φ) List.mem_cons_self (fun p => by
      rw [hrk]; exact omegaMul_nadd_lt_omegaMul_succ le_rfl _) (fun p => ?_)
  have hPp : paramsVal [φ/[numI p], ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ := by
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ hZ)
  have d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk φ)) [(∼φ)/[numI p], φ/[numI p], ψ, ∼ψ] := by
    have e : (∼φ)/[numI p] = ∼(φ/[numI p]) := by simp
    rw [e]
    have ihp := ih p
    rw [rk_subst] at ihp
    refine dlift ihp hKo (fun X => by rw [hsp p]) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) ?_
    simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty, hsp p]
    exact Set.union_subset hZ (Set.union_subset hZ (Set.union_subset hZ hZ))
  exact .exs p (hK.nadd_mem hmφ (hK.ofNat_mem _)) hPp (by rw [← hneg]; simp)
    (ofNat_lt_nadd_ofNat_succ _ p) (lt_nadd_ofNat_succ _ p) d

/-- **Lemma 6.1, stage atom** `I_k^{≺δ} t`, at level `k`. -/
theorem taut_stage (hH : ThetaVNoteD.NiceS H) (k : ℕ)
    (a : StageAt k) (t : SyntacticTerm LIinfW)
    (ih : ∀ g : StageAt k, g.1 < a.1 →
      IDwDerivable A ThetaVNoteD.zero
        (ThetaVNoteD.adjoin H (Stage.val '' params (unfoldW A k g t)))
        (ThetaVNoteD.omegaMul (rk (unfoldW A k g t)))
        [unfoldW A k g t, ∼(unfoldW A k g t)]) :
    IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (stageAt (⟨k, a⟩ : Stage) t)))
      (ThetaVNoteD.omegaMul (rk (stageAt (⟨k, a⟩ : Stage) t)))
      [stageAt (⟨k, a⟩ : Stage) t, ∼(stageAt (⟨k, a⟩ : Stage) t)] := by
  set ψ : Proposition LIinfW := stageAt (⟨k, a⟩ : Stage) t with hψ
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.1 _
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.1
  have hmψ : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 hs))
  refine .nstage (fun g => ThetaVNoteD.succ (max (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1))
    hmψ hΓ (a := a) (t := t) (List.mem_cons_of_mem _ List.mem_cons_self) (fun g hg => ?_)
    (fun g hg => ?_)
  · rw [hψ, rk_stageAt]
    refine succ_max_lt ?_ (lt_of_lt_of_le (succ_lt_omegaMul_omegaMul hg)
      (ThetaVNoteD.omegaMul_le_omegaMul (ThetaVNoteD.le_add_left _ _)))
    refine succ_omegaMul_lt ?_
    have := rk_unfold_lt_stageAt A hg t t
    rwa [rk_stageAt] at this
  · -- the premise for `g`, by clause (W) on `I_k^{≺δ} t` with the witness `g`
    set K' := ThetaVNoteD.adjoin (ThetaVNoteD.adjoin H (Stage.val '' params ψ)) {g.1} with hK'
    have hK'n : ThetaVNoteD.NiceS K' := hK.adjoin {g.1}
    have hg' : g.1 ∈ K' ∅ := subset_adjoin_empty hK.1 {g.1} rfl
    have hsub : Stage.val '' params ψ ⊆ K' ∅ :=
      hZ.trans (hK.1.mono (Set.empty_subset _))
    -- every parameter of the unfolding is `g` itself or some *lower* level's top, and every
    -- `NiceS` operator already contains every level's top unconditionally (`NiceS.Omega_mem`)
    have huP : ∀ s ∈ params (unfoldW A k g t), s.val ∈ K' ∅ := by
      intro s hs
      have := params_unfoldW A k g t hs
      rw [Set.mem_singleton_iff] at this
      subst this
      exact hg'
    have hu : Stage.val '' params (unfoldW A k g t) ⊆ K' ∅ :=
      fun _ ⟨s, hs, hx⟩ => hx ▸ huP s hs
    have hmu : ThetaVNoteD.omegaMul (rk (unfoldW A k g t)) ∈ K' ∅ :=
      hK'n.omegaMul_mem (rk_mem hK'n huP)
    have hmax : max (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1 ∈ K' ∅ := by
      rcases le_total (ThetaVNoteD.omegaMul (rk (unfoldW A k g t))) g.1 with h | h
      · rw [max_eq_right h]; exact hg'
      · rw [max_eq_left h]; exact hmu
    have hP : paramsVal [∼(unfoldW A k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hsub hsub)
    have hP2 : paramsVal [unfoldW A k g t, ∼(unfoldW A k g t), ψ, ∼ψ] ⊆ K' ∅ := by
      simp only [paramsVal_cons, paramsVal_nil, params_neg, Set.union_empty]
      exact Set.union_subset hu (Set.union_subset hu (Set.union_subset hsub hsub))
    have hop : ∀ X, ThetaVNoteD.adjoin H (Stage.val '' params (unfoldW A k g t)) X ⊆ K' X := by
      intro X
      refine hH.1.2 _ _ (Set.union_subset ?_ (hK'n.1.1 X))
      exact fun x hx => (hK'n.1.2 ∅ X (Set.empty_subset _)) (hu hx)
    have d : IDwDerivable A ThetaVNoteD.zero K' (ThetaVNoteD.omegaMul (rk (unfoldW A k g t)))
        [unfoldW A k g t, ∼(unfoldW A k g t), ψ, ∼ψ] :=
      dlift (ih g hg) hK'n.1 hop
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hP2
    exact .stage g (hK'n.succ_mem hmax) hP (a := a) (t := t)
      (List.mem_cons_of_mem _ List.mem_cons_self) hg
      (lt_of_le_of_lt (le_max_right _ _) (ThetaVNoteD.lt_succ _)) hg'
      (lt_of_le_of_lt (le_max_left _ _) (ThetaVNoteD.lt_succ _)) d

/-- **Lemma 6.1, level atom** `Jlev ℓ (s,t)`, `s`, `t` closed.  If `val s < ℓ` the rule (jlev) on
`Jlev ℓ (s,t)` and (njlev) on `¬Jlev ℓ (s,t)` reduce to the tautology for the stage atom
`I_{val s} t`, of strictly smaller rank; otherwise `¬Jlev ℓ (s,t)` is an empty conjunction. -/
theorem taut_jlev (hH : ThetaVNoteD.NiceS H) (ℓ : WithTop ℕ) {s t : SyntacticTerm LIinfW}
    (hs : s.freeVariables = ∅) (ht : t.freeVariables = ∅)
    (ih : ((termVal s : ℕ) : WithTop ℕ) < ℓ →
      IDwDerivable A ThetaVNoteD.zero
        (ThetaVNoteD.adjoin H (Stage.val '' params (IOmegaAt (termVal s) t)))
        (ThetaVNoteD.omegaMul (rk (IOmegaAt (termVal s) t)))
        [IOmegaAt (termVal s) t, ∼(IOmegaAt (termVal s) t)]) :
    IDwDerivable A ThetaVNoteD.zero
      (ThetaVNoteD.adjoin H (Stage.val '' params (jlevAt ℓ s t)))
      (ThetaVNoteD.omegaMul (rk (jlevAt ℓ s t))) [jlevAt ℓ s t, ∼(jlevAt ℓ s t)] := by
  have hp : Stage.val '' params (jlevAt ℓ s t) = ∅ := by
    rw [params_jlevAt, Set.image_empty]
  rw [hp]
  have hK := hH.adjoin ∅
  have hmψ : ThetaVNoteD.omegaMul (rk (jlevAt ℓ s t)) ∈ ThetaVNoteD.adjoin H ∅ ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun x hx => by rw [params_jlevAt] at hx; exact hx.elim))
  have hp1 : paramsVal [jlevAt ℓ s t, ∼(jlevAt ℓ s t)] ⊆ ThetaVNoteD.adjoin H ∅ ∅ := by
    simp [paramsVal_cons, paramsVal_nil, params_jlevAt]
  by_cases hv : ((termVal s : ℕ) : WithTop ℕ) < ℓ
  · set v := termVal s with hvdef
    have hIp : Stage.val '' params (IOmegaAt v t) = {ThetaVNoteD.Omega v} := by
      rw [params_IOmegaAt, Set.image_singleton]; rfl
    have hΩ : ThetaVNoteD.Omega v ∈ ThetaVNoteD.adjoin H ∅ ∅ := hK.Omega_mem v
    have hop : ∀ X, ThetaVNoteD.adjoin H (Stage.val '' params (IOmegaAt v t)) X ⊆
        ThetaVNoteD.adjoin H ∅ X := by
      intro X
      rw [hIp]
      refine hH.1.2 _ _ (Set.union_subset ?_ (fun x hx => hH.1.1 _ (Or.inr hx)))
      exact Set.singleton_subset_iff.mpr (hK.Omega_mem v)
    have hpI : paramsVal (∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) ⊆
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [paramsVal_cons, params_neg, params_IOmegaAt, Set.image_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.mpr hΩ) hp1
    have hpI2 : paramsVal (IOmegaAt v t :: ∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) ⊆
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [paramsVal_cons, params_IOmegaAt, Set.image_singleton]
      exact Set.union_subset (Set.singleton_subset_iff.mpr hΩ) hpI
    have d0 := dlift (ih hv) hK.1 hop
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil] at hx ⊢; tauto) hpI2
    have hβ : ThetaVNoteD.succ (ThetaVNoteD.omegaMul (rk (IOmegaAt v t))) ∈
        ThetaVNoteD.adjoin H ∅ ∅ := by
      rw [rk_IOmegaAt]
      exact hK.succ_mem (hK.omegaMul_mem hΩ)
    have e1 : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H ∅)
        (ThetaVNoteD.succ (ThetaVNoteD.omegaMul (rk (IOmegaAt v t))))
        (∼(IOmegaAt v t) :: [jlevAt ℓ s t, ∼(jlevAt ℓ s t)]) :=
      .jlev hβ hpI (List.mem_cons_of_mem _ List.mem_cons_self) hs ht hv
        (ThetaVNoteD.lt_succ _) d0
    exact .njlev hmψ hp1 (List.mem_cons_of_mem _ List.mem_cons_self) hs ht
      (fun _ => succ_omegaMul_lt (rk_IOmegaAt_lt_jlevAt hv t s t)) (fun _ => e1)
  · exact .njlev (α₀ := ThetaVNoteD.zero) hmψ hp1 (List.mem_cons_of_mem _ List.mem_cons_self) hs ht
      (fun h => absurd h hv) (fun h => absurd h hv)

/-- A derivation of `¬ψ, ¬¬ψ` is one of `ψ, ¬ψ`. -/
theorem taut_neg (hH : ThetaVNoteD.NiceS H) {ψ : Proposition LIinfW}
    (d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (∼ψ)))
      (ThetaVNoteD.omegaMul (rk (∼ψ))) [∼ψ, ∼(∼ψ)]) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  rw [params_neg, rk_neg] at d
  have e : ∼(∼ψ) = ψ := by simp
  rw [e] at d
  exact dswap (hH.adjoin _).1 d

/-- **Freund, Lemma 6.1**: `H[k(ψ)] ⊢^{ω·rk(ψ)}_0 ψ, ¬ψ` for every closed formula `ψ` and
every nice operator `H`. -/
theorem taut (hH : ThetaVNoteD.NiceS H) (ψ : Proposition LIinfW)
    (hc : ψ.freeVariables = ∅) :
    IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
      (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] := by
  suffices key : ∀ r : ThetaVNoteD, ∀ ψ : Proposition LIinfW, rk ψ = r → ψ.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params ψ))
        (ThetaVNoteD.omegaMul (rk ψ)) [ψ, ∼ψ] from key _ ψ rfl hc
  intro r
  induction r using WellFoundedLT.induction with
  | _ r ih =>
  intro ψ hr hc
  subst hr
  have IH : ∀ φ : Proposition LIinfW, rk φ < rk ψ → φ.freeVariables = ∅ →
      IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params φ))
        (ThetaVNoteD.omegaMul (rk φ)) [φ, ∼φ] := fun φ h hc' => ih _ h φ rfl hc'
  have hK := hH.adjoin (Stage.val '' params ψ)
  have hZ : Stage.val '' params ψ ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    subset_adjoin_empty hH.1 _
  have hα : ThetaVNoteD.omegaMul (rk ψ) ∈ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    hK.omegaMul_mem (rk_mem hK (fun s hs => mem_adjoin_params hH.1 hs))
  have hΓ : paramsVal [ψ, ∼ψ] ⊆ ThetaVNoteD.adjoin H (Stage.val '' params ψ) ∅ :=
    params_sub_adjoin hH.1
  revert IH hc hα hΓ
  cases ψ using cases0 with
  | hverum => intro _ _ hα hΓ; exact .verum hα hΓ List.mem_cons_self
  | hfalsum =>
    intro _ _ hα hΓ; exact .verum hα hΓ (List.mem_cons_of_mem _ List.mem_cons_self)
  | hrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_rel_arg hc
      have hl : IsArithLit (Semiformula.rel (Sum.inl r : LIinfW.Rel k) v) :=
        ⟨k, r, v, Or.inl rfl, hv⟩
      by_cases ht : TrueN (Semiformula.rel (Sum.inl r : LIinfW.Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.rel (Sum.inr IInfRelW.X : LIinfW.Rel 1) v = XinfAt (v 0) :=
          rel_eq_vec _ v
        have d : IDwDerivable A ThetaVNoteD.zero (ThetaVNoteD.adjoin H (Stage.val '' params (XinfAt (v 0))))
            (ThetaVNoteD.omegaMul (rk (XinfAt (v 0)))) [XinfAt (v 0), ∼(XinfAt (v 0))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_self)
            (by rw [e]; exact List.mem_cons_of_mem _ List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.rel (Sum.inr (IInfRelW.stage ⟨k, a⟩) : LIinfW.Rel 1) v =
            stageAt ⟨k, a⟩ (v 0) := rel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        rw [e]
        refine taut_stage hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e]
        have := rk_unfold_lt_stageAt A hg (v 0) (v 0)
        simpa using this
      | jlev ℓ =>
        have e : Semiformula.rel (Sum.inr (IInfRelW.jlev ℓ) : LIinfW.Rel 2) v =
            jlevAt ℓ (v 0) (v 1) := rel_eq_vec2 _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_rel_arg hc 0
        have hv1 : (v 1).freeVariables = ∅ := freeVariables_rel_arg hc 1
        rw [e]
        refine taut_jlev hH ℓ hv0 hv1 fun hl => IH _ ?_ (freeVariables_IOmegaAt hv1 _)
        rw [e]
        exact rk_IOmegaAt_lt_jlevAt hl (v 1) (v 0) (v 1)
  | hnrel k r v =>
    intro hc IH hα hΓ
    rcases r with r | r
    · have hv : ∀ i, (v i).freeVariables = ∅ := freeVariables_nrel_arg hc
      have hl : IsArithLit (Semiformula.nrel (Sum.inl r : LIinfW.Rel k) v) :=
        ⟨k, r, v, Or.inr rfl, hv⟩
      by_cases ht : TrueN (Semiformula.nrel (Sum.inl r : LIinfW.Rel k) v)
      · exact .literal hα hΓ ⟨hl, ht⟩ List.mem_cons_self
      · exact .literal hα hΓ ⟨hl.neg, (trueN_neg _).mpr ht⟩
          (List.mem_cons_of_mem _ List.mem_cons_self)
    · cases r with
      | X =>
        have e : Semiformula.nrel (Sum.inr IInfRelW.X : LIinfW.Rel 1) v = ∼(XinfAt (v 0)) :=
          nrel_eq_vec _ v
        have d : IDwDerivable A ThetaVNoteD.zero
            (ThetaVNoteD.adjoin H (Stage.val '' params (∼(XinfAt (v 0)))))
            (ThetaVNoteD.omegaMul (rk (∼(XinfAt (v 0))))) [∼(XinfAt (v 0)), ∼(∼(XinfAt (v 0)))] := by
          rw [← e]
          exact .idX (v 0) hα hΓ (by rw [e]; exact List.mem_cons_of_mem _ (by simp))
            (by rw [e]; exact List.mem_cons_self)
        rw [e]; exact d
      | stage s =>
        obtain ⟨k, a⟩ := s
        have e : Semiformula.nrel (Sum.inr (IInfRelW.stage ⟨k, a⟩) : LIinfW.Rel 1) v =
            ∼(stageAt ⟨k, a⟩ (v 0)) := nrel_eq_vec _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(stageAt ⟨k, a⟩ (v 0))) = stageAt ⟨k, a⟩ (v 0) := by simp
        rw [e2]
        refine taut_stage hH k a (v 0) fun g hg => IH _ ?_ (freeVariables_unfold k g hv0)
        rw [e, rk_neg]
        have := rk_unfold_lt_stageAt A hg (v 0) (v 0)
        simpa using this
      | jlev ℓ =>
        have e : Semiformula.nrel (Sum.inr (IInfRelW.jlev ℓ) : LIinfW.Rel 2) v =
            ∼(jlevAt ℓ (v 0) (v 1)) := nrel_eq_vec2 _ v
        have hv0 : (v 0).freeVariables = ∅ := freeVariables_nrel_arg hc 0
        have hv1 : (v 1).freeVariables = ∅ := freeVariables_nrel_arg hc 1
        rw [e]
        refine taut_neg hH ?_
        have e2 : ∼(∼(jlevAt ℓ (v 0) (v 1))) = jlevAt ℓ (v 0) (v 1) := by simp
        rw [e2]
        refine taut_jlev hH ℓ hv0 hv1 fun hl => IH _ ?_ (freeVariables_IOmegaAt hv1 _)
        rw [e, rk_neg]
        exact rk_IOmegaAt_lt_jlevAt hl (v 1) (v 0) (v 1)
  | hand φ₀ φ₁ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_and, Finset.union_eq_empty] at hc
    exact taut_and hH (IH φ₀ (rk_left_lt_and φ₀ φ₁) hc.1) (IH φ₁ (rk_right_lt_and φ₀ φ₁) hc.2)
  | hor φ₀ φ₁ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_or, Finset.union_eq_empty] at hc
    refine taut_neg hH ?_
    have e : ∼(φ₀ ⋎ φ₁) = ∼φ₀ ⋏ ∼φ₁ := by simp
    rw [e]
    refine taut_and hH (IH (∼φ₀) ?_ (by rw [Semiformula.freeVariables_not]; exact hc.1))
      (IH (∼φ₁) ?_ (by rw [Semiformula.freeVariables_not]; exact hc.2))
    · rw [rk_neg]; exact rk_left_lt_or φ₀ φ₁
    · rw [rk_neg]; exact rk_right_lt_or φ₀ φ₁
  | hall φ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_all] at hc
    exact taut_all hH fun p => IH _ (rk_subst_lt_all φ _) (freeVariables_subst_numI φ hc p)
  | hexs φ =>
    intro hc IH _ _
    rw [Semiformula.freeVariables_exs] at hc
    refine taut_neg hH ?_
    have e : ∼(∃¹ φ) = ∀¹ (∼φ) := by simp
    rw [e]
    refine taut_all hH fun p => IH _ ?_ (freeVariables_subst_numI (∼φ)
      (by rw [Semiformula.freeVariables_not]; exact hc) p)
    rw [rk_subst]
    have := rk_lt_exs φ
    rwa [rk_neg]

end Taut

end Transfer

end IDw

end OrdinalAnalysis
