/-
  Lower bounds at the transfinite levels `ω^n`.

  With the levels ordinal notations, a level-`κ` set atom is priced in the block
  `[blk κ, blk κ ⊕ ω]`, `blk κ = ω · (−1 + κ)` (`Ramified/Rank.lean`).  At the
  limit level `L = ω^n` (`n ≥ 1`) every lower block lies below
  `blk L = ω · ω^n = ω^{n+1}` (`blk_omegaPow_ofNat`), so cut ranks of derivations
  whose cut formulas have levels below `L` stay below `ω^{n+1}`.

  **The semiformal bound** (`sf_lower_omegaPow`).  A derivation in `RA_∞` (with
  the junk literals) of cut rank `ρ < ω^{n+1}` and height `h < φ_{n+1}(0)` does not
  derive transfinite induction along the coded Veblen ordering restricted to the
  segment below `φ_{n+1}(0)`.  Proof: `ρ < ω^n · m` for some `m`, and `m` steps of
  predicative cut elimination at `ξ = n` (`descend`) give a cut-free derivation of
  height `φ_n^m(h)`, which stays below the fixed point `φ_{n+1}(0)` of `φ_n`; the
  boundedness lemma refutes it.  At `n = 1` the segment is the one below `φ_2(0)`,
  at `n = 2` the one below `φ_3(0)`.

  **The finitary bound** (`ramified_lower_bound_omegaPow`).  The theory `RAlt (ω^n)`,
  names, equality and induction at every level below `ω^n`, does not prove
  transfinite induction along the segment below `φ_{n+1}(0)`: a proof uses
  finitely many axioms, all of level below `ω^n`, is replayed at a cut rank below
  `ω^{n+1}` and a height below `ε₀`, and the semiformal bound applies.  This bound
  is sound but, for the finitary theory, not claimed to be attained.
-/
import OrdinalAnalysis.Ramified.LowerBound

set_option autoImplicit false

namespace OrdinalAnalysis

namespace Ramified

open OrdinalAnalysis.Gamma0Note (veblenNote epsilonNote VeblenBelow)
open OrdinalAnalysis.Ramified.OmegaDerivableR (veblenIter veblenIter_lt_veblen)

/-! ### The levels `ω^n` -/

/-- `1 < ω^n` for `n ≥ 1`. -/
theorem one_lt_omegaPow_ofNat {n : ℕ} (hn : 1 ≤ n) :
    (1 : Gamma0Note) < Gamma0Note.omegaPow (Gamma0Note.ofNat n) := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one, Gamma0Note.repr_omegaPow, Gamma0Note.repr_ofNat]
  exact Ordinal.one_lt_omega0.trans_le
    (Ordinal.left_le_opow _ (by exact_mod_cast (show 0 < n by omega)))

/-- **`ω^n` is a limit level**, `n ≥ 1`. -/
theorem omegaPow_ofNat_limit {n : ℕ} (hn : 1 ≤ n) :
    ∀ μ < Gamma0Note.omegaPow (Gamma0Note.ofNat n),
      Gamma0Note.nadd μ 1 < Gamma0Note.omegaPow (Gamma0Note.ofNat n) :=
  fun _ hμ => Gamma0Note.nadd_lt_omegaPow hμ (one_lt_omegaPow_ofNat hn)

/-- **The base of the level-`ω^n` block is `ω^{n+1}`**, `n ≥ 1`. -/
theorem blk_omegaPow_ofNat {n : ℕ} (hn : 1 ≤ n) :
    Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.ofNat n)) =
      Gamma0Note.omegaPow (Gamma0Note.ofNat (n + 1)) := by
  rw [← Gamma0Note.repr_inj, Gamma0Note.repr_blk, Gamma0Note.repr_omegaPow,
    Gamma0Note.repr_omegaPow, Gamma0Note.repr_ofNat, Gamma0Note.repr_ofNat]
  have hω : (Ordinal.omega0 : Ordinal.{0}) ≤ Ordinal.omega0 ^ (n : Ordinal.{0}) := by
    calc (Ordinal.omega0 : Ordinal.{0}) = Ordinal.omega0 ^ (1 : Ordinal.{0}) := (Ordinal.opow_one _).symm
      _ ≤ Ordinal.omega0 ^ (n : Ordinal.{0}) :=
        Ordinal.opow_le_opow_right Ordinal.omega0_pos (by exact_mod_cast hn)
  rw [Ordinal.sub_eq_of_add_eq (Ordinal.one_add_of_omega0_le hω), omega0_mul_opow,
    ← Nat.cast_one, ← Nat.cast_add, Nat.add_comm]

/-- Every finite notation lies below `ω^n`, `n ≥ 1`. -/
theorem ofNat_lt_omegaPow_ofNat {n : ℕ} (hn : 1 ≤ n) (k : ℕ) :
    Gamma0Note.ofNat k < Gamma0Note.omegaPow (Gamma0Note.ofNat n) := by
  rw [Gamma0Note.lt_def, Gamma0Note.repr_ofNat, Gamma0Note.repr_omegaPow, Gamma0Note.repr_ofNat]
  exact (Ordinal.natCast_lt_omega0 k).trans_le
    (Ordinal.left_le_opow _ (by exact_mod_cast (show 0 < n by omega)))

open LO LO.FirstOrder LO.FirstOrder.Arithmetic

/-! ### Cut elimination below `ω^{e+1}` -/

/-- **A cut rank below `ω^{e ⊕ 1}` costs finitely many applications of `φ_e`.** -/
theorem cutFree_below_omegaPow_succ {A : Literals LRA} {I : InstantiationR} (hA : MemFree A)
    {e : Gamma0Note} (he : (1 : Gamma0Note) ≤ e) {ρ α : Gamma0Note} {Γ : Sequent LRA}
    (hρ : ρ < Gamma0Note.omegaPow (Gamma0Note.nadd e 1)) (h : OmegaDerivableR A I ρ α Γ) :
    ∃ m : ℕ, OmegaDerivableR A I 0 (veblenIter e m α) Γ := by
  obtain ⟨m, hm⟩ := Gamma0Note.exists_lt_omegaPowMul hρ
  have h' : OmegaDerivableR A I (Gamma0Note.nadd 0 (Gamma0Note.omegaPowMul e m)) α Γ := by
    rw [Gamma0Note.zero_nadd]; exact h.mono_rank hm.le
  exact ⟨m, OmegaDerivableR.descend hA he
    (fun ρ' hpc => OmegaDerivableR.rankAbsorbed_powClosed hA e he ρ' hpc) m 0
    (Gamma0Note.powClosed_zero e) h'⟩


/-! ### The semiformal bound -/

/-- **No derivation of cut rank below `blk (ω^n) = ω^{n+1}` and height below
`φ_{n+1}(0)` derives transfinite induction along the segment below `φ_{n+1}(0)`**,
`n ≥ 1`, with the junk literals among the axioms. -/
theorem sf_lower_omegaPow {n : ℕ} (hn : 1 ≤ n) {ρ h : Gamma0Note}
    (hρ : ρ < Gamma0Note.blk (Gamma0Note.omegaPow (Gamma0Note.ofNat n)))
    (hh : h < veblenNote (Gamma0Note.ofNat (n + 1)) 0) :
    ¬ OmegaDerivableR junkLitsR evInstR ρ h
      [evR (TIR (vebSegOrderR (Gamma0Note.ofNat (n + 1)) 0
        (zero_lt_ofNat_of_pos (Nat.succ_pos n))).prec)] := by
  intro hder
  rw [blk_omegaPow_ofNat hn, Gamma0Note.ofNat_succ_eq_nadd_one] at hρ
  obtain ⟨m, hd⟩ := cutFree_below_omegaPow_succ memFree_junkLitsR
    (Gamma0Note.one_le_ofNat hn) hρ hder
  have hβ : veblenIter (Gamma0Note.ofNat n) m h < veblenNote (Gamma0Note.ofNat (n + 1)) 0 :=
    veblenIter_lt_veblen (Gamma0Note.ofNat_lt_ofNat (Nat.lt_succ_self n)) 0 m h hh
  have : OrdinalNotation (VeblenBelow (Gamma0Note.ofNat (n + 1)) 0) :=
    Gamma0Note.VeblenBelow.ordinalNotation _ _ (zero_lt_ofNat_of_pos (Nat.succ_pos n))
  exact not_derivable_TI_R_junk _ (Below.mk _ hβ) (OmegaDerivableR.toBelow hd hβ)

/-! ### The finitary bound -/

/-- **`RA_{<ω^n}` does not prove transfinite induction along the segment below
`φ_{n+1}(0)`**, `n ≥ 1`: at `n = 2`, the theory with names at every level below
`ω^2` does not prove `TI` along the segment below `φ_3(0)`. -/
theorem ramified_lower_bound_omegaPow {n : ℕ} (hn : 1 ≤ n) :
    RAlt (Gamma0Note.omegaPow (Gamma0Note.ofNat n)) ⊬
      (Semiformula.univCl (TIR (vebSegOrderR (Gamma0Note.ofNat (n + 1)) 0
        (zero_lt_ofNat_of_pos (Nat.succ_pos n))).prec) : Sentence LRA) := by
  rintro ⟨h⟩
  set L := Gamma0Note.omegaPow (Gamma0Note.ofNat n) with hLdef
  set C := vebSegOrderR (Gamma0Note.ofNat (n + 1)) 0 (zero_lt_ofNat_of_pos (Nat.succ_pos n))
    with hCdef
  have hL1 : 1 ≤ L := (one_lt_omegaPow_ofNat hn).le
  obtain ⟨ν, k, α, hν, hα, hd⟩ := provable_rank_height_of_exists (RAlt L)
    (fun τ hτ => RAlt_axiom_derivable_lt_epsilon hL1 τ hτ) h
  have hνL : ν < L := by
    rcases hν with rfl | ⟨τ, hτ, rfl⟩
    · exact lt_of_lt_of_le Gamma0Note.zero_lt_one hL1
    · exact lvlOf_emb_lt_of_mem_RAlt hL1 hτ
  have hρ : Gamma0Note.nadd (Gamma0Note.blkTop ν) (Gamma0Note.ofNat k) < Gamma0Note.blk L := by
    have h1 : Gamma0Note.blkTop ν < Gamma0Note.blk L :=
      Gamma0Note.blkTop_lt_blk_of_limit (omegaPow_ofNat_limit hn) hνL
    rw [hLdef, blk_omegaPow_ofNat hn] at h1 ⊢
    exact Gamma0Note.nadd_lt_omegaPow h1 (ofNat_lt_omegaPow_ofNat (Nat.succ_pos n) k)
  have hαlt : α < veblenNote (Gamma0Note.ofNat (n + 1)) 0 :=
    lt_trans hα (Gamma0Note.veblenNote_zero_lt_veblenNote_zero
      (by rw [← Gamma0Note.ofNat_one]; exact Gamma0Note.ofNat_lt_ofNat (by omega)))
  have hemb : (Rewriting.emb (Semiformula.univCl (TIR C.prec)) : Proposition LRA) = TIR C.prec :=
    emb_univCl_of_freeVariables_eq_empty (CodedOrderR.freeVariables_TIR C)
  rw [hemb] at hd
  exact sf_lower_omegaPow hn hρ hαlt (hd.mono_lits trueArithLitsR_le_junkLitsR)

end Ramified

end OrdinalAnalysis
