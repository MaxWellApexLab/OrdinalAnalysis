/-
  The generalised descent `(D^β)` in `RA_∞`.

  For a notation `β` and a level `L = ρ ⊕ ω^β` ending in `ω^β` (`ρ` a multiple of
  `ω^β`), and every notation `c`,

      ⊢^{H}_{blkTop (L+1)}  ¬Acc_{L+1}(c̄), Acc_L(φ_{1+β}(c)‾),

  where `Acc_μ(v) :≡ ∀z TI(≺₁, v, λx. x ∈̇_μ z)`, the cut rank `blkTop (L+1)` is
  `blk (L+1) ⊕ ω`, and the height is `H = ε₀ ⊕ ω^{(1+β) ⊕ 1}` (`descentBeta`).
  At `β = 1`: from `Acc_{L+1}(c)` to `Acc_L(φ_2(c))` for every `L` ending in `ω`
  (`descentBeta_one`).

  ## The recursion

  The statement is proved for the Veblen index `a = 1 + β ≥ 1`, with the level
  ending in `ω^{−1+a}`, by well-founded induction on `a : Gamma0Note`
  (`descentAt_all`).

  * `a = 1`: `(D^0)` with the value `ε_c = φ_1(c)` (`descentOne`).
  * `a = a' ⊕ 1`, `a' ≥ 1` (`descent_succ`): Steps 1 and 2 (`assemble`); the
    instances of Step 1 are, for `ξ < φ_a(γ)` and a name `z` whose effective body
    has level `κ < L`:
    - `γ = 0`: `ξ < φ_{a'}^m(0)` (`succCover_zero`); from `Acc(0)`, `m`
      applications of `(D)` at the index `a'` along the levels
      `N_j = P ⊕ ω^{−1+a'}·j` (`chain`), all below `L` and above `κ`
      (`levelRoom`), give `Acc_{κ+1}` below `φ_{a'}^m(0)`;
    - `γ = g ⊕ 1`: `ξ < φ_{a'}^m(φ_a(g) ⊕ 1)` (`succCover_succ`); the hypothesis
      gives `Acc_L(φ_a(g))`, then `Acc_L(φ_a(g) ⊕ 1)` (`succD`), then the chain;
    - `γ` a limit: `ξ < φ_a(g)` for some `g < γ` (`succCover_limit`); the
      hypothesis suffices.
    Each instance ends with `lastStep`, which copies `z` down to the level of the
    parameter-free code of its effective body.
  * `a` a limit (`descent_limit`): the same with a single application of `(D)` at
    an index `a'' < a` (`limitCover_zero`, `limitCover_succ`, `limitCover_limit`),
    at a level `N = P ⊕ ω^{−1+a''}` between `κ` and `L`.

  The levels used by the instance at `z` depend on `z`, and the chain length on
  `ξ`: unboundedly many levels below `L`, collected by the ω-rules of `accIntro`.

  ## Heights

  Every derivation obtained from outside the calculus has height below `ε₀`, and a
  cut costs one above the larger premise.  So the chain of `m` applications of
  `(D)` at `a'` stays below `hgtD a' ⊕ (2m + 1)`, every instance below
  `bndD a = (ε₀ ⊕ ω^a) ⊕ ω`, and `(D)` at `a` below `bndD a ⊕ 24 < hgtD a`.
  `hgtD a < ε_b` for `a < ε_b`, `b > 0`, and more generally `hgtD a < λ` for every
  `a < λ`, `λ > ε₀` a fixed point of `ω^·` (`hgtD_lt_of_fixed`).
-/
import OrdinalAnalysis.Ramified.DescentBetaAux6
import OrdinalAnalysis.Ordinal.Veblen.FundSeq
import OrdinalAnalysis.Ramified.SemiformalLower

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified


/-! ### Ordinal arithmetic on the notations -/

section Notation

open Ordinal

theorem predNote_nadd_one {a : Gamma0Note} (ha : 1 ≤ a) :
    Gamma0Note.predNote (Gamma0Note.nadd a 1) = Gamma0Note.nadd (Gamma0Note.predNote a) 1 := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_predNote, Gamma0Note.repr_nadd_one, Gamma0Note.repr_nadd_one,
    Gamma0Note.repr_predNote]
  have h1 : (1 : Ordinal) ≤ Gamma0Note.repr a := by
    rw [Gamma0Note.le_def, Gamma0Note.repr_one] at ha; exact ha
  have e : Gamma0Note.repr a = 1 + (Gamma0Note.repr a - 1) :=
    (Ordinal.add_sub_cancel_of_le h1).symm
  conv_lhs => rw [e, add_assoc, Ordinal.add_sub_cancel]

theorem predNote_of_limit {a : Gamma0Note} (ha : Order.IsSuccLimit (Gamma0Note.repr a)) :
    Gamma0Note.predNote a = a := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_predNote]
  have hω : ω ≤ Gamma0Note.repr a := Ordinal.omega0_le_of_isSuccLimit ha
  conv_lhs => rw [← Ordinal.one_add_of_omega0_le hω]
  exact Ordinal.add_sub_cancel _ _

theorem predNote_one : Gamma0Note.predNote 1 = 0 := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_predNote, Gamma0Note.repr_one, Gamma0Note.repr_zero, Ordinal.sub_self]

theorem predNote_le (a : Gamma0Note) : Gamma0Note.predNote a ≤ a := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_predNote]
  exact Ordinal.sub_le_self _ _

theorem predNote_onePlusNote (β : Gamma0Note) :
    Gamma0Note.predNote (Gamma0Note.onePlusNote β) = β := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_predNote, Gamma0Note.repr_onePlusNote, Ordinal.add_sub_cancel]

theorem one_le_onePlusNote' (β : Gamma0Note) : (1 : Gamma0Note) ≤ Gamma0Note.onePlusNote β := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_onePlusNote, Gamma0Note.repr_one]
  exact le_self_add

theorem onePlusNote_one : Gamma0Note.onePlusNote 1 = Gamma0Note.ofNat 2 := by
  apply Gamma0Note.repr_injective
  rw [Gamma0Note.repr_onePlusNote, Gamma0Note.repr_one, Gamma0Note.repr_ofNat]
  norm_num

theorem one_lt_of_limit {a : Gamma0Note} (ha : Order.IsSuccLimit (Gamma0Note.repr a)) :
    (1 : Gamma0Note) < a := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one]
  exact lt_of_lt_of_le Ordinal.one_lt_omega0 (Ordinal.omega0_le_of_isSuccLimit ha)

theorem nadd_one_lt_of_limit {a b : Gamma0Note} (ha : Order.IsSuccLimit (Gamma0Note.repr a))
    (hb : b < a) : Gamma0Note.nadd b 1 < a := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_nadd_one, ← Order.succ_eq_add_one]
  exact ha.succ_lt (Gamma0Note.lt_def.mp hb)


/-! ### Levels ending in `ω^e` -/

/-- **`L` ends in `ω^e`**: `L = ρ ⊕ ω^e` with `ρ` a multiple of `ω^e`. -/
def EndsIn (e L : Gamma0Note) : Prop :=
  ∃ ρ : Gamma0Note, Gamma0Note.PowClosed e ρ ∧ L = Gamma0Note.nadd ρ (Gamma0Note.omegaPow e)

theorem EndsIn.pos {e L : Gamma0Note} (h : EndsIn e L) : 0 < L := by
  obtain ⟨ρ, -, rfl⟩ := h
  exact lt_of_lt_of_le (Gamma0Note.omegaPow_pos e) (Gamma0Note.le_nadd_right _ _)

/-- **Room below a level ending in `ω^E`.**  For `e < E` and `κ < ρ ⊕ ω^E`, there is
a multiple `P > κ` of `ω^e` such that every `P ⊕ ω^e·j` stays, with its successor,
below `ρ ⊕ ω^E`. -/
theorem levelRoom {E e ρ κ : Gamma0Note} (heE : e < E) (hρ : Gamma0Note.PowClosed E ρ)
    (hκ : κ < Gamma0Note.nadd ρ (Gamma0Note.omegaPow E)) :
    ∃ P : Gamma0Note, Gamma0Note.PowClosed e P ∧ κ < P ∧
      ∀ j : ℕ, Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e j)) 1 <
        Gamma0Note.nadd ρ (Gamma0Note.omegaPow E) := by
  have hE0 : 0 < E := lt_of_le_of_lt (Gamma0Note.zero_le_note e) heE
  obtain ⟨d, hd, hκd⟩ := Gamma0Note.exists_lt_nadd_omegaPow hE0 hρ hκ
  set f := max e (Gamma0Note.leadExpNote d) with hfdef
  have hf : f < E := max_lt heE (Gamma0Note.leadExpNote_lt_of_lt_omegaPow hE0 hd)
  have hdf : d < Gamma0Note.omegaPow (Gamma0Note.nadd f 1) :=
    lt_of_lt_of_le (Gamma0Note.lt_omegaPow_leadExp_succ d)
      (Gamma0Note.omegaPow_le_omegaPow (Gamma0Note.nadd_le_nadd_left 1 (le_max_right _ _)))
  obtain ⟨k, hk⟩ := Gamma0Note.exists_lt_omegaPowMul hdf
  have hρf : Gamma0Note.PowClosed f ρ := hρ.mono (le_of_lt hf)
  obtain ⟨hPf, hPr⟩ := Gamma0Note.powClosed_nadd_omegaPowMul hρf k
  set P := Gamma0Note.nadd ρ (Gamma0Note.omegaPowMul f k) with hPdef
  have hPe : Gamma0Note.PowClosed e P := hPf.mono (le_max_left _ _)
  refine ⟨P, hPe, lt_of_lt_of_le hκd (Gamma0Note.nadd_le_nadd_right ρ (le_of_lt hk)), fun j => ?_⟩
  obtain ⟨-, hPj⟩ := Gamma0Note.powClosed_nadd_omegaPowMul hPe j
  rw [Gamma0Note.lt_def, Gamma0Note.repr_nadd_one, hPj, hPr, Gamma0Note.repr_nadd_omegaPow hρ]
  have hP : Ordinal.IsPrincipal (· + ·) (ω ^ Gamma0Note.repr E) :=
    Ordinal.isPrincipal_add_omega0_opow _
  have h1 : ω ^ Gamma0Note.repr f * (k : Ordinal) < ω ^ Gamma0Note.repr E :=
    Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 k) (Gamma0Note.lt_def.mp hf)
  have h2 : ω ^ Gamma0Note.repr e * (j : Ordinal) < ω ^ Gamma0Note.repr E :=
    Ordinal.opow_mul_lt_opow (Ordinal.natCast_lt_omega0 j) (Gamma0Note.lt_def.mp heE)
  have h3 : (1 : Ordinal) < ω ^ Gamma0Note.repr E := by
    rw [← Ordinal.opow_zero ω]
    exact (Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).2
      (by rw [Gamma0Note.lt_def, Gamma0Note.repr_zero] at hE0; exact hE0)
  have h4 : ω ^ Gamma0Note.repr f * (k : Ordinal) + ω ^ Gamma0Note.repr e * (j : Ordinal) + 1 <
      ω ^ Gamma0Note.repr E := hP (hP h1 h2) h3
  calc Gamma0Note.repr ρ + ω ^ Gamma0Note.repr f * (k : Ordinal) +
        ω ^ Gamma0Note.repr e * (j : Ordinal) + 1
      = Gamma0Note.repr ρ + (ω ^ Gamma0Note.repr f * (k : Ordinal) +
          ω ^ Gamma0Note.repr e * (j : Ordinal) + 1) := by simp only [add_assoc]
    _ < Gamma0Note.repr ρ + ω ^ Gamma0Note.repr E := add_lt_add_right h4 _

/-- Consecutive levels of a chain are at least one apart. -/
theorem nadd_omegaPowMul_succ_le {e P : Gamma0Note} (hP : Gamma0Note.PowClosed e P) (m : ℕ) :
    Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e m)) 1 ≤
      Gamma0Note.nadd P (Gamma0Note.omegaPowMul e (m + 1)) := by
  rw [Gamma0Note.le_def, Gamma0Note.repr_nadd_one, (Gamma0Note.powClosed_nadd_omegaPowMul hP m).2,
    (Gamma0Note.powClosed_nadd_omegaPowMul hP (m + 1)).2, Nat.cast_add, Nat.cast_one, mul_add,
    mul_one]
  have h1 : (1 : Ordinal) ≤ ω ^ Gamma0Note.repr e :=
    Order.one_le_iff_pos.2 (Ordinal.opow_pos _ Ordinal.omega0_pos)
  calc Gamma0Note.repr P + ω ^ Gamma0Note.repr e * (m : Ordinal) + 1
      ≤ Gamma0Note.repr P + ω ^ Gamma0Note.repr e * (m : Ordinal) + ω ^ Gamma0Note.repr e :=
        add_le_add_right h1 _
    _ = Gamma0Note.repr P + (ω ^ Gamma0Note.repr e * (m : Ordinal) + ω ^ Gamma0Note.repr e) :=
        add_assoc _ _ _

theorem endsIn_chain {e P : Gamma0Note} (hP : Gamma0Note.PowClosed e P) (m : ℕ) :
    EndsIn e (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e (m + 1))) :=
  ⟨Gamma0Note.nadd P (Gamma0Note.omegaPowMul e m), (Gamma0Note.powClosed_nadd_omegaPowMul hP m).1,
    by rw [Gamma0Note.omegaPowMul_succ, Gamma0Note.nadd_assoc]⟩

end Notation

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)

/-! ### Heights -/

/-- **The height of `(D)` at the Veblen index `a`**: `ε₀ ⊕ ω^{a ⊕ 1}`. -/
def hgtD (a : Gamma0Note) : Gamma0Note :=
  Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.omegaPow (Gamma0Note.nadd a 1))

/-- The common bound of the instances of Step 1 at the index `a`: `(ε₀ ⊕ ω^a) ⊕ ω`. -/
def bndD (a : Gamma0Note) : Gamma0Note :=
  Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.omegaPow a))
    (Gamma0Note.omegaPow 1)

theorem ofNat_lt_omegaPow_of_one_le {x : Gamma0Note} (hx : (1 : Gamma0Note) ≤ x) (n : ℕ) :
    Gamma0Note.ofNat n < Gamma0Note.omegaPow x :=
  lt_of_lt_of_le (ofNat_lt_omegaPow_one n) (Gamma0Note.omegaPow_le_omegaPow hx)

theorem eps_le_hgtD (a : Gamma0Note) : Gamma0Note.epsilonNote 0 ≤ hgtD a :=
  Gamma0Note.le_nadd_left _ _

theorem eps_le_bndD (a : Gamma0Note) : Gamma0Note.epsilonNote 0 ≤ bndD a :=
  le_trans (Gamma0Note.le_nadd_left _ _) (Gamma0Note.le_nadd_left _ _)

theorem eps_nadd_le_hgtD (a : Gamma0Note) (n : ℕ) :
    Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat n) ≤ hgtD a :=
  Gamma0Note.nadd_le_nadd_right _
    (le_of_lt (ofNat_lt_omegaPow_of_one_le (Gamma0Note.one_le_nadd_one a) n))

theorem eps_nadd_le_bndD (a : Gamma0Note) (n : ℕ) :
    Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat n) ≤ bndD a :=
  le_trans (Gamma0Note.nadd_le_nadd_right _ (le_of_lt (ofNat_lt_omegaPow_one n)))
    (Gamma0Note.nadd_le_nadd_left _ (Gamma0Note.le_nadd_left _ _))

theorem hgtD_nadd_lt_bndD_succ (a' : Gamma0Note) (n : ℕ) :
    Gamma0Note.nadd (hgtD a') (Gamma0Note.ofNat n) < bndD (Gamma0Note.nadd a' 1) :=
  Gamma0Note.nadd_lt_nadd_right _ (ofNat_lt_omegaPow_one n)

theorem hgtD_nadd_lt_bndD_of_lt {a'' a : Gamma0Note} (h : Gamma0Note.nadd a'' 1 < a)
    (n : ℕ) : Gamma0Note.nadd (hgtD a'') (Gamma0Note.ofNat n) < bndD a := by
  have ha : (1 : Gamma0Note) ≤ a :=
    le_trans (Gamma0Note.one_le_nadd_one a'') (le_of_lt h)
  refine lt_of_lt_of_le ?_ (Gamma0Note.le_nadd_left _ _)
  rw [hgtD, Gamma0Note.nadd_assoc]
  exact Gamma0Note.nadd_lt_nadd_right _ (Gamma0Note.nadd_lt_omegaPow
    (Gamma0Note.omegaPow_lt_omegaPow h) (ofNat_lt_omegaPow_of_one_le ha n))

theorem bndD_nadd_lt_hgtD {a : Gamma0Note} (ha : (1 : Gamma0Note) ≤ a) (n : ℕ) :
    Gamma0Note.nadd (bndD a) (Gamma0Note.ofNat n) < hgtD a := by
  rw [bndD, hgtD, Gamma0Note.nadd_assoc, Gamma0Note.nadd_assoc]
  have h1 : (1 : Gamma0Note) < Gamma0Note.nadd a 1 :=
    lt_of_le_of_lt ha (Gamma0Note.lt_nadd_one a)
  exact Gamma0Note.nadd_lt_nadd_right _ (Gamma0Note.nadd_lt_omegaPow
    (Gamma0Note.omegaPow_lt_omegaPow (Gamma0Note.lt_nadd_one a))
    (Gamma0Note.nadd_lt_omegaPow (Gamma0Note.omegaPow_lt_omegaPow h1)
      (ofNat_lt_omegaPow_of_one_le (le_of_lt h1) n)))

/-- **The heights stay below every fixed point of `ω^·` above `ε₀` and the index.** -/
theorem hgtD_lt_of_fixed {lam a : Gamma0Note} (hlam : Gamma0Note.omegaPow lam = lam)
    (hε : Gamma0Note.epsilonNote 0 < lam) (ha : a < lam) : hgtD a < lam := by
  have h1 : (1 : Gamma0Note) < lam := lt_of_le_of_lt
    (le_trans (Gamma0Note.one_le_omegaPow 0) (by
      rw [Gamma0Note.le_def, Gamma0Note.repr_omegaPow, Gamma0Note.repr_zero,
        Ordinal.opow_zero, ← Gamma0Note.repr_one, ← Gamma0Note.le_def]
      exact le_of_lt (lt_of_le_of_lt (Gamma0Note.one_le_omegaPow 0) (by
        rw [Gamma0Note.lt_def, Gamma0Note.repr_omegaPow, Gamma0Note.repr_zero,
          Ordinal.opow_zero, Gamma0Note.repr_epsilonNote_eq_epsilon]
        exact Ordinal.one_lt_omega0.trans (Ordinal.omega0_lt_epsilon 0))))) hε
  have hs : Gamma0Note.nadd a 1 < lam := by
    rw [← hlam]; exact Gamma0Note.nadd_lt_omegaPow (hlam.symm ▸ ha) (hlam.symm ▸ h1)
  rw [hgtD, ← hlam]
  exact Gamma0Note.nadd_lt_omegaPow (hlam.symm ▸ hε)
    (Gamma0Note.omegaPow_lt_omegaPow hs)

/-- **The heights stay below `ε_b`, `b > 0`, at every index below `ε_b`.** -/
theorem hgtD_lt_epsilon {a b : Gamma0Note} (hb : 0 < b) (ha : a < Gamma0Note.epsilonNote b) :
    hgtD a < Gamma0Note.epsilonNote b :=
  hgtD_lt_of_fixed (Gamma0Note.omegaPow_epsilonNote b) (Gamma0Note.epsilon_lt_epsilon hb) ha

/-! ### The statement -/

/-- **`(D)` at the Veblen index `a` and the level `L`**: for every notation `c`,
`¬Acc_{L+1}(c̄), Acc_L(φ_a(c)‾)`, at cut rank `blkTop (L ⊕ 1)`, below `hgtD a`. -/
def DescentAt (a L : Gamma0Note) : Prop :=
  ∀ c : Gamma0Note, DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
    [evR (∼accA (Gamma0Note.nadd L 1) (gamma0Code c)),
      evR (accA L (gamma0Code (Gamma0Note.veblenNote a c)))] (hgtD a)

/-! ### Tools for the instances -/

variable {ρ : Gamma0Note}

/-- Pass `Acc` along a derivable implication `Acc_μ(y) → Acc_κ(y')`. -/
theorem transfer {μ κ : Lv} {y y' : ℕ} {Γ : Sequent LRA} {H H' : Gamma0Note}
    (hrk : rank (accA μ y) < ρ) (hT : DerLt ρ [evR (∼accA μ y), evR (accA κ y')] H)
    (hA : DerLt ρ (evR (accA μ y) :: Γ) H) (hH : H < H') :
    DerLt ρ (evR (accA κ y') :: Γ) H' := by
  rw [evR_neg] at hT
  exact (DerLt.cutHyp (by rw [rank_evR]; exact hrk) hT hA hH).weak (by subset_tac)

theorem rank_accA_lt {μ L : Lv} (h : μ ≤ L) (y : ℕ) :
    rank (accA μ y) < Gamma0Note.blkTop (Gamma0Note.nadd L 1) :=
  rank_lt_of_lvlOf_le (le_trans (lvlOf_accA_le μ y) h)

theorem blkTop_le_of_le {μ L : Lv} (h : μ ≤ L) :
    Gamma0Note.blkTop (Gamma0Note.nadd μ 1) ≤ Gamma0Note.blkTop (Gamma0Note.nadd L 1) :=
  Gamma0Note.blkTop_mono (Gamma0Note.nadd_le_nadd_left 1 h)

/-- **The hypothesis `∀y ≺₁ γ. F_{a,L}(y)` gives `Acc_L(φ_a(g))` for `g < γ`.** -/
theorem accFromHyp {a : Gamma0Note} {L : Lv} {g γ : Gamma0Note} (hg : g < γ) {H : Gamma0Note}
    (hH : Gamma0Note.epsilonNote 0 ≤ H) (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd L 1) ≤ ρ) :
    DerLt ρ [evR (accA L (gamma0Code (Gamma0Note.veblenNote a g))),
      evR (∼hypF (vebF a L) (gamma0Code γ))] (Gamma0Note.nadd H (Gamma0Note.ofNat 4)) := by
  have hd := DerLt.discharge (ρ := ρ) (C := accA L (gamma0Code (Gamma0Note.veblenNote a g)))
    (Γ := [evR (∼hypF (vebF a L) (gamma0Code γ))]) (H := H)
    [hypF (vebF a L) (gamma0Code γ), precA (gamma0Code g) (gamma0Code γ),
      vebA (gamma0Code (Gamma0Note.veblenNote a g)) (gamma0Code a) (gamma0Code g)]
    (freeVariables_accA _ _)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact freeVariables_hypF (freeVariables_vebF a L) _
      · exact freeVariables_precA _ _
      · exact freeVariables_vebA _ _ _)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f (hypF (vebF a L) (gamma0Code γ)) := hAs _ List.mem_cons_self
      have h2 : Semiformula.Eval ![] f (precA (gamma0Code g) (gamma0Code γ)) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h3 : Semiformula.Eval ![] f
          (vebA (gamma0Code (Gamma0Note.veblenNote a g)) (gamma0Code a) (gamma0Code g)) :=
        hAs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      rw [eval_hypF] at h1
      rw [eval_precA] at h2
      rw [eval_vebA] at h3
      show Semiformula.Eval ![] f (accA L (gamma0Code (Gamma0Note.veblenNote a g)))
      rw [eval_accA]
      have hF := h1 _ h2
      rw [eval_vebF] at hF
      exact hF _ h3)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (lvlOf_hypF_le (lvlOf_vebF_le a L) _)) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := L)
          (by rw [lvlOf_precA]; exact gamma0_zero_le L)) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := L)
          (by rw [lvlOf_vebA]; exact gamma0_zero_le L)) hρ)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact (DerLt.identity (evR (hypF (vebF a L) (gamma0Code γ))) hH).weak
          (by simp only [evR_neg]; subset_tac)
      · exact (DerLt.of_true (rFree_arAt _ _) (freeVariables_precA _ _) (precA_true_code hg)
          hH).weak (by subset_tac)
      · exact (DerLt.of_true (rFree_arAt _ _) (freeVariables_vebA _ _ _)
          ((vebA_true_iff _ _ _).mpr ⟨a, g, rfl, rfl, rfl⟩) hH).weak (by subset_tac))
    hρ1 hH
  simp only [List.length_cons, List.length_nil] at hd
  exact hd

/-- **The instance at a limit `γ`**: `ξ < φ_a(g)` for some `g < γ`, and the
hypothesis suffices. -/
theorem limitInst {a : Gamma0Note} {L : Lv} {g γ ξ : Gamma0Note} (hg : g < γ)
    (hξ : ξ < Gamma0Note.veblenNote a g) (z : ℕ) (hρ1 : Gamma0Note.omegaPow 1 ≤ ρ)
    (hρ : Gamma0Note.blkTop (Gamma0Note.nadd L 1) ≤ ρ) :
    DerLt ρ [evR (∼progA L z), evR (memA L (gamma0Code ξ) z),
      evR (∼hypF (vebF a L) (gamma0Code γ))]
      (Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat 8)) := by
  set E := Gamma0Note.epsilonNote 0
  set e := Gamma0Note.veblenNote a g
  have hE4 : E ≤ Gamma0Note.nadd E (Gamma0Note.ofNat 4) := le_nadd_ofNat E 4
  have h0 := accFromHyp (a := a) (L := L) hg (le_refl E) hρ1 hρ
  have hd := DerLt.discharge (ρ := ρ) (C := memA L (gamma0Code ξ) z)
    (Γ := [evR (∼progA L z), evR (∼hypF (vebF a L) (gamma0Code γ))])
    (H := Gamma0Note.nadd E (Gamma0Note.ofNat 4))
    [accA L (gamma0Code e), progA L z, precA (gamma0Code ξ) (gamma0Code e)]
    (freeVariables_memA _ _ _)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact freeVariables_accA _ _
      · exact freeVariables_progA _ _
      · exact freeVariables_precA _ _)
    (by
      intro M _ _ f hAs
      have h1 : Semiformula.Eval ![] f (accA L (gamma0Code e)) := hAs _ List.mem_cons_self
      have h2 : Semiformula.Eval ![] f (progA L z) :=
        hAs _ (List.mem_cons_of_mem _ List.mem_cons_self)
      have h3 : Semiformula.Eval ![] f (precA (gamma0Code ξ) (gamma0Code e)) :=
        hAs _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      rw [eval_accA] at h1
      rw [eval_progA] at h2
      rw [eval_precA] at h3
      show Semiformula.Eval ![] f (memA L (gamma0Code ξ) z)
      rw [eval_memA]
      exact h1 (numVal M z) h2 _ h3)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (lvlOf_accA_le L _)) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (le_of_eq (lvlOf_progA L z))) hρ
      · exact lt_of_lt_of_le (rank_lt_of_lvlOf_le (L := L)
          (by rw [lvlOf_precA]; exact gamma0_zero_le L)) hρ)
    (by
      intro A hA
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hA
      rcases hA with rfl | rfl | rfl
      · exact h0.weak (by subset_tac)
      · exact ((DerLt.identity (evR (progA L z)) (le_refl E)).weak
          (by simp only [evR_neg]; subset_tac)).mono hE4
      · exact ((DerLt.of_true (rFree_arAt _ _) (freeVariables_precA _ _) (precA_true_code hξ)
          (le_refl E)).weak (by subset_tac)).mono hE4)
    hρ1 hE4
  simp only [List.length_cons, List.length_nil] at hd
  rw [nadd_ofNat_add] at hd
  exact hd.weak (by subset_tac)

theorem lt_nadd_ofNat_one (H : Gamma0Note) : H < Gamma0Note.nadd H (Gamma0Note.ofNat 1) :=
  lt_of_le_of_lt (le_of_eq (Gamma0Note.nadd_zero H).symm)
    (nadd_ofNat_lt_nadd_ofNat H (by norm_num : 0 < 1))

theorem eps_le_hgtD_nadd (a : Gamma0Note) (n : ℕ) :
    Gamma0Note.epsilonNote 0 ≤ Gamma0Note.nadd (hgtD a) (Gamma0Note.ofNat n) :=
  le_trans (eps_le_hgtD a) (le_nadd_ofNat _ n)

theorem eps_nadd_le_hgtD_nadd (a : Gamma0Note) (m n : ℕ) :
    Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.ofNat m) ≤
      Gamma0Note.nadd (hgtD a) (Gamma0Note.ofNat n) :=
  le_trans (eps_nadd_le_hgtD a m) (le_nadd_ofNat _ n)

/-! ### The chain -/

/-- **The chain**: `m` applications of `(D)` at the index `a'`, along the levels
`N_j = P ⊕ ω^{−1+a'}·j` below `L`, with copies between consecutive levels:
`¬Acc_{N_m+1}(ȳ), Acc_{P+1}(φ_{a'}^m(y)‾)`, below `hgtD a' ⊕ (2m + 1)`. -/
theorem chain {a' : Gamma0Note}
    (IH : ∀ N : Lv, EndsIn (Gamma0Note.predNote a') N → DescentAt a' N)
    {L P : Lv} (hP : Gamma0Note.PowClosed (Gamma0Note.predNote a') P)
    (hroom : ∀ j : ℕ, Gamma0Note.nadd (Gamma0Note.nadd P
      (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') j)) 1 < L) :
    ∀ (m : ℕ) (y : Gamma0Note), DerLt (Gamma0Note.blkTop (Gamma0Note.nadd L 1))
      [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd P
          (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') m)) 1) (gamma0Code y)),
        evR (accA (Gamma0Note.nadd P 1) (gamma0Code (Gamma0Note.phiIter a' m y)))]
      (Gamma0Note.nadd (hgtD a') (Gamma0Note.ofNat (2 * m + 1)))
  | 0, y => by
      have e0 : Gamma0Note.nadd P (Gamma0Note.omegaPowMul (Gamma0Note.predNote a') 0) = P := by
        rw [Gamma0Note.omegaPowMul_zero, Gamma0Note.nadd_zero]
      have hPL : Gamma0Note.nadd P 1 ≤ L := by
        have h := hroom 0
        rw [e0] at h
        exact le_of_lt h
      rw [e0]
      exact copyD le_rfl (gamma0Code y) (blkTop_le_of_le hPL) (eps_le_hgtD_nadd a' _)
  | (m + 1), y => by
      set e' := Gamma0Note.predNote a' with he'
      have hNL : ∀ j : ℕ, Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' j) ≤ L := fun j =>
        le_trans (le_of_lt (Gamma0Note.lt_nadd_one _)) (le_of_lt (hroom j))
      have hN1L : ∀ j : ℕ, Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' j)) 1 ≤ L :=
        fun j => le_of_lt (hroom j)
      have hD := (IH _ (endsIn_chain hP m) y).mono_rank (blkTop_le_of_le (hNL (m + 1)))
      have hC := copyD (ρ := Gamma0Note.blkTop (Gamma0Note.nadd L 1))
        (nadd_omegaPowMul_succ_le hP m) (gamma0Code (Gamma0Note.veblenNote a' y))
        (blkTop_le_of_le (hNL (m + 1))) (eps_le_hgtD a')
      have T1 := transfer (Γ := [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd P
          (Gamma0Note.omegaPowMul e' (m + 1))) 1) (gamma0Code y))])
        (rank_accA_lt (hNL (m + 1)) _) hC (hD.weak (by subset_tac))
        (lt_nadd_ofNat_one (hgtD a'))
      have R := chain IH hP hroom m (Gamma0Note.veblenNote a' y)
      have T2 := transfer (rank_accA_lt (hN1L m) _) R
        (T1.mono (nadd_ofNat_le_nadd_ofNat _ (by omega)))
        (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 1)))
      have hit : Gamma0Note.phiIter a' (m + 1) y =
          Gamma0Note.phiIter a' m (Gamma0Note.veblenNote a' y) :=
        Function.iterate_succ_apply _ m y
      rw [hit]
      exact (T2.weak (by subset_tac)).mono (nadd_ofNat_le_nadd_ofNat _ (by omega))

/-! ### The successor step -/

/-- **`(D)` at `a' ⊕ 1` from `(D)` at `a'`**, `a' ≥ 1`. -/
theorem descent_succ {a' : Gamma0Note} (ha' : (1 : Gamma0Note) ≤ a')
    (IH : ∀ N : Lv, EndsIn (Gamma0Note.predNote a') N → DescentAt a' N) {L : Lv}
    (hL : EndsIn (Gamma0Note.predNote (Gamma0Note.nadd a' 1)) L) :
    DescentAt (Gamma0Note.nadd a' 1) L := by
  rw [predNote_nadd_one ha'] at hL
  have hL0 : 0 < L := hL.pos
  obtain ⟨ρ0, hρ0, hLeq⟩ := hL
  set e' := Gamma0Note.predNote a' with he'
  set ρL := Gamma0Note.blkTop (Gamma0Note.nadd L 1) with hρL
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρL := omegaPow_one_le_blkTop (nadd_one_ne_zero L)
  set E := Gamma0Note.epsilonNote 0 with hE
  intro c
  refine (assemble (B := bndD (Gamma0Note.nadd a' 1)) (eps_le_bndD _) ?_ c).mono
    (le_of_lt (bndD_nadd_lt_hgtD (Gamma0Note.one_le_nadd_one a') 24))
  intro γ ξ z hξ
  set κ := lvlOf (effBodyAt L z) with hκdef
  have hκL : κ < L := lvlOf_effBodyAt_lt hL0 z
  obtain ⟨P, hP, hκP, hroom'⟩ := levelRoom (Gamma0Note.lt_nadd_one e') hρ0 (hLeq ▸ hκL)
  have hroom : ∀ j : ℕ, Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' j)) 1 < L :=
    fun j => hLeq ▸ hroom' j
  set κ' := Gamma0Note.nadd κ 1 with hκ'def
  have hκκ' : κ < κ' := Gamma0Note.lt_nadd_one κ
  have hκ'P : κ' ≤ P := Gamma0Note.nadd_one_le_of_lt hκP
  have hP1L : Gamma0Note.nadd P 1 ≤ L := by
    have h := hroom 0
    rw [Gamma0Note.omegaPowMul_zero, Gamma0Note.nadd_zero] at h
    exact le_of_lt h
  have hκ'P1 : κ' ≤ Gamma0Note.nadd P 1 := le_trans hκ'P (le_of_lt (Gamma0Note.lt_nadd_one P))
  have hκ'L : κ' ≤ L := le_trans hκ'P1 hP1L
  have hch := chain IH hP hroom
  have hNm : ∀ m : ℕ, Gamma0Note.nadd (Gamma0Note.nadd P (Gamma0Note.omegaPowMul e' m)) 1 ≤ L :=
    fun m => le_of_lt (hroom m)
  rcases Gamma0Note.zero_or_exists_pred_or_isSuccLimit γ with rfl | ⟨g, rfl⟩ | hlim
  · -- `γ = 0`
    obtain ⟨m, hm⟩ := Gamma0Note.succCover_zero hξ
    have h0 := accZeroD (ρ := ρL) hρ1 (blkTop_le_of_le (hNm m)) (Γ := []) (le_refl E)
    have t1 := transfer (rank_accA_lt (hNm m) _) (hch m 0)
      (h0.mono (eps_nadd_le_hgtD_nadd a' 6 (2 * m + 1)))
      (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 1)))
    have cp := copyD (ρ := ρL) hκ'P1 (gamma0Code (Gamma0Note.phiIter a' m 0))
      (blkTop_le_of_le hP1L) (eps_le_hgtD_nadd a' (2 * m + 2))
    have t2 := transfer (rank_accA_lt hP1L _) cp t1
      (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 2)))
    have ls := lastStep hκ'L z hκκ' hm (eps_le_hgtD_nadd a' _) hρ1 le_rfl t2
    rw [nadd_ofNat_add] at ls
    exact (ls.weak (by subset_tac)).mono (le_of_lt (hgtD_nadd_lt_bndD_succ a' _))
  · -- `γ = g ⊕ 1`
    obtain ⟨m, hm⟩ := Gamma0Note.succCover_succ hξ
    set e := Gamma0Note.veblenNote (Gamma0Note.nadd a' 1) g with he
    have h0 := accFromHyp (a := Gamma0Note.nadd a' 1) (L := L) (Gamma0Note.lt_nadd_one g)
      (le_refl E) hρ1 le_rfl
    have hs := succD (ρ := ρL) (μ := L) hρ1 le_rfl e
    rw [nadd_ofNat_add] at hs
    have t0 := transfer (rank_accA_lt le_rfl _) hs
      (h0.mono (nadd_ofNat_le_nadd_ofNat E (by norm_num : 4 ≤ 10)))
      (nadd_ofNat_lt_nadd_ofNat E (by norm_num : 10 < 11))
    have cL := copyD (ρ := ρL) (hNm m) (gamma0Code (Gamma0Note.nadd e 1)) le_rfl
      (epsilon_le_nadd (le_refl E) 11)
    have t1 := transfer (rank_accA_lt le_rfl _) cL t0
      (nadd_ofNat_lt_nadd_ofNat E (by norm_num : 11 < 12))
    have t2 := transfer (rank_accA_lt (hNm m) _)
      ((hch m (Gamma0Note.nadd e 1)).mono (nadd_ofNat_le_nadd_ofNat _ (by omega :
        2 * m + 1 ≤ 2 * m + 12)))
      (t1.mono (eps_nadd_le_hgtD_nadd a' 12 (2 * m + 12)))
      (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 12)))
    have cp := copyD (ρ := ρL) hκ'P1 (gamma0Code (Gamma0Note.phiIter a' m (Gamma0Note.nadd e 1)))
      (blkTop_le_of_le hP1L) (eps_le_hgtD_nadd a' (2 * m + 13))
    have t3 := transfer (rank_accA_lt hP1L _) cp t2
      (nadd_ofNat_lt_nadd_ofNat (hgtD a') (Nat.lt_succ_self (2 * m + 13)))
    have ls := lastStep hκ'L z hκκ' hm (eps_le_hgtD_nadd a' _) hρ1 le_rfl t3
    rw [nadd_ofNat_add] at ls
    exact (ls.weak (by subset_tac)).mono (le_of_lt (hgtD_nadd_lt_bndD_succ a' _))
  · -- `γ` a limit
    obtain ⟨g, hg, hξg⟩ := Gamma0Note.succCover_limit hlim hξ
    exact (limitInst hg hξg z hρ1 le_rfl).mono (eps_nadd_le_bndD _ 8)

/-! ### The base, and `β = 1` -/

/-- **`(D)` at the index `1`**: `(D^0)`, the value `ε_c = φ_1(c)`. -/
theorem descent_one {L : Lv} (hL : EndsIn (Gamma0Note.predNote 1) L) : DescentAt 1 L :=
  fun c => (descentOne hL.pos c).mono (eps_nadd_le_hgtD 1 10)

/-- **`(D)` at the index `2`**, the first derivation of the new kind: for every
level `L` ending in `ω`, `¬Acc_{L+1}(c̄), Acc_L(φ_2(c)‾)`. -/
theorem descent_two {L : Lv} (hL : EndsIn 1 L) : DescentAt (Gamma0Note.nadd 1 1) L := by
  have h1 : Gamma0Note.predNote (Gamma0Note.nadd 1 1) = 1 := by
    rw [predNote_nadd_one le_rfl, predNote_one, Gamma0Note.zero_nadd]
  exact descent_succ le_rfl (fun N hN => descent_one hN) (by rw [h1]; exact hL)

/-! ### The limit step -/

/-- **`(D)` at a limit index `a` from `(D)` below `a`.** -/
theorem descent_limit {a : Gamma0Note} (ha : Order.IsSuccLimit (Gamma0Note.repr a))
    (IH : ∀ a'' < a, (1 : Gamma0Note) ≤ a'' →
      ∀ N : Lv, EndsIn (Gamma0Note.predNote a'') N → DescentAt a'' N)
    {L : Lv} (hL : EndsIn (Gamma0Note.predNote a) L) : DescentAt a L := by
  rw [predNote_of_limit ha] at hL
  have hL0 : 0 < L := hL.pos
  obtain ⟨ρ0, hρ0, hLeq⟩ := hL
  set ρL := Gamma0Note.blkTop (Gamma0Note.nadd L 1) with hρL
  have hρ1 : Gamma0Note.omegaPow 1 ≤ ρL := omegaPow_one_le_blkTop (nadd_one_ne_zero L)
  set E := Gamma0Note.epsilonNote 0 with hE
  have h1a : (1 : Gamma0Note) < a := one_lt_of_limit ha
  intro c
  refine (assemble (B := bndD a) (eps_le_bndD a) ?_ c).mono
    (le_of_lt (bndD_nadd_lt_hgtD (le_of_lt h1a) 24))
  intro γ ξ z hξ
  set κ := lvlOf (effBodyAt L z) with hκdef
  have hκL : κ < L := lvlOf_effBodyAt_lt hL0 z
  set κ' := Gamma0Note.nadd κ 1 with hκ'def
  have hκκ' : κ < κ' := Gamma0Note.lt_nadd_one κ
  -- a level `N` ending in `ω^{−1+a''}`, between `κ'` and `L`
  have room : ∀ a'' : Gamma0Note, a'' < a → ∃ N : Lv,
      EndsIn (Gamma0Note.predNote a'') N ∧ κ' ≤ N ∧ Gamma0Note.nadd N 1 ≤ L := by
    intro a'' ha''
    have he : Gamma0Note.predNote a'' < a := lt_of_le_of_lt (predNote_le a'') ha''
    obtain ⟨P, hP, hκP, hroom⟩ := levelRoom he hρ0 (hLeq ▸ hκL)
    refine ⟨Gamma0Note.nadd P (Gamma0Note.omegaPowMul (Gamma0Note.predNote a'') (0 + 1)),
      endsIn_chain hP 0, le_trans (Gamma0Note.nadd_one_le_of_lt hκP) (Gamma0Note.le_nadd_left _ _),
      le_of_lt (hLeq ▸ hroom 1)⟩
  rcases Gamma0Note.zero_or_exists_pred_or_isSuccLimit γ with rfl | ⟨g, rfl⟩ | hlim
  · -- `γ = 0`
    obtain ⟨β'', hβ, hξβ⟩ := Gamma0Note.limitCover_zero ha hξ
    set a'' := max β'' 1 with ha''def
    have ha''a : a'' < a := max_lt hβ h1a
    have ha''1 : (1 : Gamma0Note) ≤ a'' := le_max_right _ _
    have hξ' : ξ < Gamma0Note.veblenNote a'' 0 :=
      lt_of_lt_of_le hξβ (Gamma0Note.veblenNote_le_veblenNote_left (le_max_left _ _))
    obtain ⟨N, hNe, hκ'N, hN1L⟩ := room a'' ha''a
    have hNL : N ≤ L := le_trans (le_of_lt (Gamma0Note.lt_nadd_one N)) hN1L
    have hD := (IH a'' ha''a ha''1 N hNe 0).mono_rank (blkTop_le_of_le hNL)
    have h0 := accZeroD (ρ := ρL) hρ1 (blkTop_le_of_le hN1L) (Γ := []) (le_refl E)
    have t1 := transfer (rank_accA_lt hN1L _) hD (h0.mono (eps_nadd_le_hgtD a'' 6))
      (lt_nadd_ofNat_one (hgtD a''))
    have cp := copyD (ρ := ρL) hκ'N (gamma0Code (Gamma0Note.veblenNote a'' 0))
      (blkTop_le_of_le hNL) (eps_le_hgtD_nadd a'' 1)
    have t2 := transfer (rank_accA_lt hNL _) cp t1
      (nadd_ofNat_lt_nadd_ofNat (hgtD a'') (by norm_num : 1 < 2))
    have ls := lastStep (le_trans hκ'N hNL) z hκκ' hξ' (eps_le_hgtD_nadd a'' _) hρ1 le_rfl t2
    rw [nadd_ofNat_add] at ls
    exact (ls.weak (by subset_tac)).mono
      (le_of_lt (hgtD_nadd_lt_bndD_of_lt (nadd_one_lt_of_limit ha ha''a) _))
  · -- `γ = g ⊕ 1`
    obtain ⟨β'', hβ, hξβ⟩ := Gamma0Note.limitCover_succ ha hξ
    set a'' := max β'' 1 with ha''def
    have ha''a : a'' < a := max_lt hβ h1a
    have ha''1 : (1 : Gamma0Note) ≤ a'' := le_max_right _ _
    set e := Gamma0Note.veblenNote a g with he
    have hξ' : ξ < Gamma0Note.veblenNote a'' (Gamma0Note.nadd e 1) :=
      lt_of_lt_of_le hξβ (Gamma0Note.veblenNote_le_veblenNote_left (le_max_left _ _))
    obtain ⟨N, hNe, hκ'N, hN1L⟩ := room a'' ha''a
    have hNL : N ≤ L := le_trans (le_of_lt (Gamma0Note.lt_nadd_one N)) hN1L
    have h0 := accFromHyp (a := a) (L := L) (Gamma0Note.lt_nadd_one g) (le_refl E) hρ1 le_rfl
    have hs := succD (ρ := ρL) (μ := L) hρ1 le_rfl e
    rw [nadd_ofNat_add] at hs
    have t0 := transfer (rank_accA_lt le_rfl _) hs
      (h0.mono (nadd_ofNat_le_nadd_ofNat E (by norm_num : 4 ≤ 10)))
      (nadd_ofNat_lt_nadd_ofNat E (by norm_num : 10 < 11))
    have cL := copyD (ρ := ρL) hN1L (gamma0Code (Gamma0Note.nadd e 1)) le_rfl
      (epsilon_le_nadd (le_refl E) 11)
    have t1 := transfer (rank_accA_lt le_rfl _) cL t0
      (nadd_ofNat_lt_nadd_ofNat E (by norm_num : 11 < 12))
    have hD := (IH a'' ha''a ha''1 N hNe (Gamma0Note.nadd e 1)).mono_rank (blkTop_le_of_le hNL)
    have t2 := transfer (rank_accA_lt hN1L _) hD (t1.mono (eps_nadd_le_hgtD a'' 12))
      (lt_nadd_ofNat_one (hgtD a''))
    have cp := copyD (ρ := ρL) hκ'N
      (gamma0Code (Gamma0Note.veblenNote a'' (Gamma0Note.nadd e 1)))
      (blkTop_le_of_le hNL) (eps_le_hgtD_nadd a'' 1)
    have t3 := transfer (rank_accA_lt hNL _) cp t2
      (nadd_ofNat_lt_nadd_ofNat (hgtD a'') (by norm_num : 1 < 2))
    have ls := lastStep (le_trans hκ'N hNL) z hκκ' hξ' (eps_le_hgtD_nadd a'' _) hρ1 le_rfl t3
    rw [nadd_ofNat_add] at ls
    exact (ls.weak (by subset_tac)).mono
      (le_of_lt (hgtD_nadd_lt_bndD_of_lt (nadd_one_lt_of_limit ha ha''a) _))
  · -- `γ` a limit
    obtain ⟨g, hg, hξg⟩ := Gamma0Note.limitCover_limit hlim hξ
    exact (limitInst hg hξg z hρ1 le_rfl).mono (eps_nadd_le_bndD _ 8)

/-! ### The recursion on the index -/

/-- **`(D)` at every Veblen index `a ≥ 1` and every level ending in `ω^{−1+a}`**, by
well-founded recursion on `a : Gamma0Note`. -/
theorem descentAt_all (a : Gamma0Note) :
    (1 : Gamma0Note) ≤ a → ∀ L : Lv, EndsIn (Gamma0Note.predNote a) L → DescentAt a L := by
  refine WellFounded.induction Gamma0Note.lt_wf (C := fun a => (1 : Gamma0Note) ≤ a →
    ∀ L : Lv, EndsIn (Gamma0Note.predNote a) L → DescentAt a L) a ?_
  intro a IH ha L hL
  rcases Gamma0Note.zero_or_exists_pred_or_isSuccLimit a with rfl | ⟨a', rfl⟩ | hlim
  · exact absurd ha (not_le.mpr Gamma0Note.zero_lt_one)
  · by_cases ha' : a' = 0
    · subst ha'
      rw [Gamma0Note.zero_nadd] at hL ⊢
      exact descent_one hL
    · have ha'1 : (1 : Gamma0Note) ≤ a' :=
        Gamma0Note.one_le_of_pos (lt_of_le_of_ne (Gamma0Note.zero_le_note a') (Ne.symm ha'))
      exact descent_succ ha'1 (IH a' (Gamma0Note.lt_nadd_one a') ha'1) hL
  · exact descent_limit hlim (fun a'' h h1 => IH a'' h h1) hL

/-! ### The headlines -/

/-- The cut rank of `(D)` at the level `L` is `blk (L ⊕ 1) ⊕ ω`. -/
theorem blkTop_nadd_one_eq (L : Lv) :
    Gamma0Note.blkTop (Gamma0Note.nadd L 1) =
      Gamma0Note.nadd (Gamma0Note.blk (Gamma0Note.nadd L 1)) (Gamma0Note.omegaPow 1) :=
  Gamma0Note.blkTop_of_ne_zero (nadd_one_ne_zero L)

/-- **The generalised descent `(D^β)`.**  For every notation `β`, every level
`L = ρ ⊕ ω^β` with `ρ` a multiple of `ω^β`, and every notation `c`,

    ⊢ ¬Acc_{L+1}(c̄), Acc_L(φ_{1+β}(c)‾)

in `RA_∞` with the junk literals, at cut rank `blkTop (L ⊕ 1) = blk (L ⊕ 1) ⊕ ω` and
height `hgtD (1 + β) = ε₀ ⊕ ω^{(1+β) ⊕ 1}`.  Here
`Acc_μ(v) = accA μ v = (tiMuR μ)/[v̄]`. -/
theorem descentBeta (β ρ : Gamma0Note) (hρ : Gamma0Note.PowClosed β ρ) (c : Gamma0Note) :
    OmegaDerivableR junkLitsR evInstR
      (Gamma0Note.blkTop (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.omegaPow β)) 1))
      (hgtD (Gamma0Note.onePlusNote β))
      [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.omegaPow β)) 1) (gamma0Code c)),
        evR (accA (Gamma0Note.nadd ρ (Gamma0Note.omegaPow β))
          (gamma0Code (Gamma0Note.veblenNote (Gamma0Note.onePlusNote β) c)))] := by
  have hE : EndsIn (Gamma0Note.predNote (Gamma0Note.onePlusNote β))
      (Gamma0Note.nadd ρ (Gamma0Note.omegaPow β)) := by
    rw [predNote_onePlusNote]
    exact ⟨ρ, hρ, rfl⟩
  exact (descentAt_all _ (one_le_onePlusNote' β) _ hE c).toDer

/-- **`(D^β)` at `β = 1`**: for every level `L = ρ ⊕ ω` (`ρ` a multiple of `ω`) and
every notation `c`, `⊢ ¬Acc_{L+1}(c̄), Acc_L(φ_2(c)‾)`, at cut rank
`blkTop (L ⊕ 1)` and height `ε₀ ⊕ ω^3`. -/
theorem descentBeta_one (ρ : Gamma0Note) (hρ : Gamma0Note.PowClosed 1 ρ) (c : Gamma0Note) :
    OmegaDerivableR junkLitsR evInstR
      (Gamma0Note.blkTop (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.omegaPow 1)) 1))
      (hgtD (Gamma0Note.ofNat 2))
      [evR (∼accA (Gamma0Note.nadd (Gamma0Note.nadd ρ (Gamma0Note.omegaPow 1)) 1) (gamma0Code c)),
        evR (accA (Gamma0Note.nadd ρ (Gamma0Note.omegaPow 1))
          (gamma0Code (Gamma0Note.veblenNote (Gamma0Note.ofNat 2) c)))] := by
  have h := descentBeta 1 ρ hρ c
  rwa [onePlusNote_one] at h

/-- The height of `(D^β)` at `β = 1` is `ε₀ ⊕ ω^3`. -/
theorem hgtD_two : hgtD (Gamma0Note.ofNat 2) =
    Gamma0Note.nadd (Gamma0Note.epsilonNote 0) (Gamma0Note.omegaPow (Gamma0Note.ofNat 3)) := by
  rw [hgtD, ← Gamma0Note.ofNat_succ_eq_nadd_one]

/-! ### Axiom audit -/

#print axioms OmegaDerivableR.invOr
#print axioms DerLt.discharge
#print axioms accIntro
#print axioms step2
#print axioms descentOne
#print axioms assemble
#print axioms levelRoom
#print axioms chain
#print axioms descent_succ
#print axioms descent_limit
#print axioms descent_two
#print axioms descentAt_all
#print axioms descentBeta
#print axioms descentBeta_one
#print axioms hgtD_lt_of_fixed
#print axioms hgtD_lt_epsilon

end Ramified

end OrdinalAnalysis
