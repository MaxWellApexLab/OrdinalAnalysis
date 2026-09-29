/-
  The rank of the formulas of the infinitary language `LIinfW` of `ID_ω`.

  Source: the design notes §3.1 "Language `LIinfW`", read for the
  headline lemma list; `IDn/Rank.lean` is the template for everything about the stage predicates
  `I_k^{≺α}` (levels `k : ℕ` unbounded here, `IDn`'s `Fin n` dropped throughout — `IDw/Language.
  lean`'s `Stage := Σ k : ℕ, StageAt k` already made this change once, at the language level; this
  file makes the same change at the rank level, so the outer `variable {n : ℕ}` of `IDn.Rank`
  disappears entirely).

      rk(I_k^{≺α} t) := rk(¬I_k^{≺α} t) := Ω_k + ω·α                    (unchanged from `IDn`),
      rk(Jlev k (s,t)) := rk(¬Jlev k (s,t))                   := Ω_k + 1  (k : ℕ, so also `k = 0`:
                                                                  `Ω_0 + 1 = 1`, the design's own
                                                                  "`Jlev 0`: 1" aside — `OmegaBelow
                                                                  0 = zero`, not a separate case),
      rk(Jlev ⊤ (s,t)) := rk(¬Jlev ⊤ (s,t))                   := Ω_ω     (`ThetaVNoteD.OmegaW`),
      rk(ψ₀ ∨ ψ₁) := rk(ψ₀ ∧ ψ₁)    := max{rk ψ₀, rk ψ₁} + 1,
      rk(∃x ψ)    := rk(∀x ψ)       := rk ψ + 1.

  `Ω_k` is `OmegaBelow k` (defined below on `ThetaVNoteD`, same convention as `ThetaWNoteD.
  OmegaBelow`: `OmegaBelow 0 := 0`, `OmegaBelow (m+1) := ThetaVNoteD.Omega m`). `+` is the
  *ordinary* ordinal sum; `Jlev`'s `+ 1` coincides with `ThetaVNoteD.succ` either way
  (`add_one_eq_succ`).

  **Why no `OrdinalNotation`-generic section.** `IDn.Rank`'s final `Generic` section
  (`rk_and_succ`, …) rewrites the successor of the rank definition as `OrdinalNotation.succ`,
  using `ThetaWNoteD`'s registered `OrdinalNotation` instance (`ThetaW/Instance.lean`). No such
  instance exists yet for `ThetaVNoteD` (`ThetaVNoteD.ordinalNotation` is stage `N1w`'s, still
  in flight — confirmed absent by `dispatch_gate.py check L`, current HEAD); the *arithmetic*
  this file actually needs (`add`, `nadd`, `omegaPow`, `omegaMul`, `ofNat`, `succ`, their `dom_*`
  lemmas — `ThetaV/Arith.lean`, independently `lean_warm.py`-verified green) is already merged
  and is all that is used below, so that section is simply omitted, not stubbed.

  **The laws proved** (mirroring `IDn/Rank.lean`'s list, plus the `Jlev`/limit additions of the
  design's §3.1 ranks paragraph):

    * `rk (∼φ) = rk φ`, and the rank does not see terms (`rk_rew`, `rk_subst`);
    * **the stage case, at level `k`** (unchanged from `IDn`): `rk(unfoldW A k g t) ≺ Ω_k + ω·a'
      = rk(I_k^{≺a'} s)` for `g ≺ a'` at level `k` (`rk_unfold_lt_stageAt`), via the finite-part
      bound `rk(unfoldW A k g t) ⪯ (Ω_k + ω·g) ⊕ p` (`rk_unfold_le`) — genuinely *simpler* than
      `IDn`'s version: `unfoldW`'s parameter set is *exactly* `{⟨k,g⟩}` (`IDw.params_unfoldW`,
      finished alongside this file, §3 below), so there is no "other levels' own top" case to
      discharge and no `LevelBounded` hypothesis to carry;
    * `rk(I_k^{≺a} t) ≺ Ω_{k+1}` for `a ≺ Ω_{k+1}`, and `rk(I_k t) = Ω_{k+1}` (`rk_IOmegaAt`);
    * **a formula of rank `≺ Ω_{k+1}` has every stage parameter of level `≤ k` and `≠ Stage.top
      k`** — the per-level `rk_lt_Omega_iff` (`Jlev` atoms never obstruct this: `params (Jlev …)
      = ∅`, so the `Jlev` cases of the induction are immediate, unlike the stage cases);
    * bounding at level `k` does not raise the rank (`rk_capAt_le`; `Jlev` is a fixed point of
      `capAt`, `capAt_jlevAt`/`capAt_njlevAt`, so its atom-rank bound is `le_refl`);
    * **the limit**: a formula containing no *positive* `Jlev ⊤` literal, and whose every `Jlev`
      literal's level and every stage parameter are finite, has rank `≺ Ω_ω` (`rk_lt_OmegaW`) —
      the `Ω_ω`-analogue of `rk_lt_Omega_iff`, proved the same way (structural induction, `Jlev
      ⊤`'s atom rank `OmegaW` is the only one *not* `≺ OmegaW`, everything else is);
    * **the embedded `LXJ`-formulas**: `embedW`'s only new atom is `Jlev ⊤` (`J ↦ Jlev ⊤`), whose
      rank is exactly `OmegaW`, so `rk (embed φ) ≤ OmegaW + ofNat φ.complexity`
      (`rk_embed_le_OmegaW_add_ofNat`) — the promised "`rk (embedW φ) ≤ OmegaW + ofNat m`-type"
      bound, `m` read as the logical complexity (`params (embed φ) = ∅`, `IDw.params_embed`, so
      the finite-part bound's hypothesis is vacuous here).
-/
import OrdinalAnalysis.IDw.Language
import OrdinalAnalysis.Ordinal.ThetaV.Arith

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### `ThetaVNoteD` helpers needed for the rank (ported from `IDn.Rank`'s `ThetaWNoteD` section,
`ThetaWNoteD`/`ThetaWTerm` replaced by `ThetaVNoteD`/`ThetaVTerm`, plus the new `OmegaW` facts
needed for the limit rank `Ω_ω`). -/

namespace ThetaVTerm

theorem addL_zero_ne_nil : ∀ L : List ThetaVTerm, addL [sum []] L ≠ []
  | [] => by simp [addL]
  | y :: ys => by rw [addL_cons]; simp

/-- `0 ≺ 1 + e`. -/
theorem nil_lt_onePlus (e : ThetaVTerm) : sum [] < onePlus e := by
  apply nil_lt_of_ne
  intro h
  exact addL_zero_ne_nil (toList e) (ofList_injective (h.trans ofList_nil.symm))

/-- If `xs` is lexicographically below `ys`, then appending zero exponents to `xs` after raising
every exponent by `1 +` keeps it below `ys` raised the same way. -/
theorem sum_map_onePlus_append_lt {zs : List ThetaVTerm} (hz : ∀ z ∈ zs, z = sum []) :
    ∀ {xs ys : List ThetaVTerm}, List.Lex (· < ·) xs ys → (∀ x ∈ xs, NF x) →
      (∀ y ∈ ys, NF y) → sum (xs.map onePlus ++ zs) < sum (ys.map onePlus) := by
  intro xs ys h hx hy
  induction h with
  | nil =>
    simp only [List.map_nil, List.nil_append, List.map_cons]
    exact sum_lt_cons_of_forall_lt _ (fun z hz' => by rw [hz z hz']; exact nil_lt_onePlus _)
  | rel h =>
    simp only [List.map_cons, List.cons_append]
    exact (cons_lt_cons_iff _ _ _ _).mpr
      (Or.inl (onePlus_lt_onePlus (hx _ List.mem_cons_self) (hy _ List.mem_cons_self) h))
  | cons _ ih =>
    simp only [List.map_cons, List.cons_append]
    exact (cons_lt_cons_iff _ _ _ _).mpr (Or.inr ⟨rfl,
      ih (fun x hx' => hx x (List.mem_cons_of_mem _ hx'))
        (fun y hy' => hy y (List.mem_cons_of_mem _ hy'))⟩)

end ThetaVTerm

namespace ThetaVNoteD

theorem zero_le' (x : ThetaVNoteD) : zero ≤ x := by rw [← bot_eq_zero]; exact bot_le

theorem zero_lt_Omega (k : ℕ) : zero < Omega k := by
  rw [lt_iff_entries, entries_zero, entries_Omega]; exact ThetaVTerm.nil_lt_cons _ _

theorem zero_lt_OmegaW : zero < OmegaW := lt_trans (zero_lt_Omega 0) (Omega_lt_OmegaW 0)

theorem omegaMul_le_omegaMul {a b : ThetaVNoteD} (h : a ≤ b) : omegaMul a ≤ omegaMul b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaMul_lt_omegaMul h)
  · exact le_refl _

theorem ofNat_le_ofNat {p q : ℕ} (h : p ≤ q) : ofNat p ≤ ofNat q := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (ofNat_lt_ofNat h)
  · exact le_refl _

theorem nadd_le_nadd_left' {a a' : ThetaVNoteD} (b : ThetaVNoteD) (h : a ≤ a') :
    nadd a b ≤ nadd a' b := by
  rw [nadd_comm a b, nadd_comm a' b]; exact nadd_le_nadd_right b h

theorem succ_le_succ {a b : ThetaVNoteD} (h : a ≤ b) : succ a ≤ succ b :=
  nadd_le_nadd_left' one h

theorem lt_of_succ_lt {x p : ThetaVNoteD} (h : succ x < p) : x < p := lt_trans (lt_succ x) h

/-- `succ x ≺ p ↔ x ≺ p`, for principal `p`. -/
theorem succ_lt_prin_iff {x p : ThetaVNoteD} (hp : ThetaVTerm.IsPrin p.1) : succ x < p ↔ x < p :=
  ⟨lt_of_succ_lt, succ_lt_prin hp⟩

/-- **`Ω_k`, `k ∈ ℕ`, with `Ω_0 := 0`** (`ThetaVNoteD.Omega m` already denotes `Ω_{m+1}`). -/
def OmegaBelow : ℕ → ThetaVNoteD
  | 0 => zero
  | k + 1 => Omega k

@[simp] theorem OmegaBelow_zero : OmegaBelow 0 = zero := rfl

@[simp] theorem OmegaBelow_succ (k : ℕ) : OmegaBelow (k + 1) = Omega k := rfl

theorem Omega_lt_Omega_iff {i j : ℕ} : Omega i < Omega j ↔ i < j := by
  rw [lt_iff]; exact ThetaVTerm.Omega_lt_Omega_iff i j

theorem le_add_right (a b : ThetaVNoteD) : a ≤ a + b := by
  conv_lhs => rw [← add_zero a]
  exact add_le_add_left a (zero_le' b)

/-- **`Ω_k ≺ Ω_{k+1}`.** -/
theorem OmegaBelow_lt_Omega (k : ℕ) : OmegaBelow k < Omega k := by
  cases k with
  | zero => rw [OmegaBelow_zero, lt_iff_entries, entries_zero, entries_Omega]
            exact ThetaVTerm.nil_lt_cons _ _
  | succ m => rw [OmegaBelow_succ]; exact Omega_lt_Omega_iff.mpr (Nat.lt_succ_self m)

/-- **`Ω_j ⪯ Ω_k` for `j ≺ k`.** -/
theorem Omega_le_OmegaBelow_of_lt {j k : ℕ} (h : j < k) : Omega j ≤ OmegaBelow k := by
  cases k with
  | zero => exact absurd h (Nat.not_lt_zero j)
  | succ m =>
    rw [OmegaBelow_succ]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | rfl
    · exact le_of_lt (Omega_lt_Omega_iff.mpr h')
    · exact le_refl _

/-- **`Ω_k ≺ Ω_ω`, every level.** -/
theorem OmegaBelow_lt_OmegaW (k : ℕ) : OmegaBelow k < OmegaW := by
  cases k with
  | zero => exact zero_lt_OmegaW
  | succ m => rw [OmegaBelow_succ]; exact Omega_lt_OmegaW m

/-- `x + n = x ⊕ n`: the ordinary sum and the natural sum agree when the right summand is a
numeral. -/
theorem add_ofNat_eq_nadd_ofNat (x : ThetaVNoteD) (p : ℕ) : x + ofNat p = nadd x (ofNat p) := by
  induction p with
  | zero => rw [ofNat_zero, add_zero, nadd_zero]
  | succ p ih =>
    have e1 : x + ofNat (p + 1) = succ (nadd x (ofNat p)) := by
      rw [ofNat_succ, ← add_one_eq_succ, ← add_assoc, ih, add_one_eq_succ]
    have e2 : nadd x (ofNat (p + 1)) = succ (nadd x (ofNat p)) := by
      rw [ofNat_succ]
      show nadd x (nadd (ofNat p) one) = nadd (nadd x (ofNat p)) one
      rw [nadd_assoc]
    rw [e1, e2]

/-- `(x ⊕ p) + 1 = x ⊕ (p + 1)`, for the successor clause of `rk`. -/
theorem succ_add_ofNat (x : ThetaVNoteD) (p : ℕ) : succ (x + ofNat p) = x + ofNat (p + 1) := by
  rw [← add_one_eq_succ, add_assoc, add_one_eq_succ, ← ofNat_succ]

theorem entries_omegaMul_nadd_ofNat (a : ThetaVNoteD) (p : ℕ) :
    (nadd (omegaMul a) (ofNat p)).entries =
      a.entries.map ThetaVTerm.onePlus ++ List.replicate p (ThetaVTerm.sum []) := by
  have hs : ThetaVTerm.SortedDesc (a.entries.map ThetaVTerm.onePlus) := by
    have := sorted_entries (omegaMul a); rwa [entries_omegaMul] at this
  have hr : ThetaVTerm.SortedDesc (List.replicate p (ThetaVTerm.sum [])) :=
    List.pairwise_replicate.mpr (Or.inr (ThetaVTerm.le_refl' _))
  rw [entries_nadd, entries_omegaMul, entries_ofNat]
  refine ThetaVTerm.mergeL_eq_of_perm hs hr ?_ (List.Perm.refl _)
  refine List.pairwise_append.mpr ⟨hs, hr, fun x _ y hy => ?_⟩
  rw [List.eq_of_mem_replicate hy]
  exact ThetaVTerm.nil_le x

/-- **`ω · a ⊕ p ≺ ω · b` for `a ≺ b`**: a finite part never reaches the next multiple of `ω`. -/
theorem omegaMul_nadd_ofNat_lt {a b : ThetaVNoteD} (h : a < b) (p : ℕ) :
    nadd (omegaMul a) (ofNat p) < omegaMul b := by
  rw [lt_iff_entries, entries_omegaMul_nadd_ofNat, entries_omegaMul]
  exact ThetaVTerm.sum_map_onePlus_append_lt (fun _ hz => List.eq_of_mem_replicate hz)
    ((ThetaVTerm.sum_lt_sum_iff_lex _ _).mp (lt_iff_entries.mp h))
    (fun _ hx => (cnf_entries a).nf hx) (fun _ hy => (cnf_entries b).nf hy)

/-- **`(x + ω·a) ⊕ p ≺ x + ω·b` for `a ≺ b`**, `x` any fixed prefix — the `Ω_k +`-wrapped form of
`omegaMul_nadd_ofNat_lt` used for the stage rank drop at level `k` (`x := OmegaBelow k`). -/
theorem add_omegaMul_nadd_ofNat_lt (x : ThetaVNoteD) {a b : ThetaVNoteD} (h : a < b) (p : ℕ) :
    nadd (x + omegaMul a) (ofNat p) < x + omegaMul b := by
  rw [← add_ofNat_eq_nadd_ofNat, add_assoc, add_ofNat_eq_nadd_ofNat]
  exact add_lt_add_left x (omegaMul_nadd_ofNat_lt h p)

/-- `Ω_ω` is a fixed point of `ω ·` (`IsPrin OmegaW`). -/
theorem omegaMul_OmegaW : omegaMul OmegaW = OmegaW := omegaMul_prin ThetaVTerm.isPrin_OmegaW

/-- `Ω_ω` is a fixed point of `ω^·` (`IsPrin OmegaW`). -/
theorem omegaPow_OmegaW : omegaPow OmegaW = OmegaW :=
  omegaPow_eq_self_iff.mpr ThetaVTerm.isPrin_OmegaW

/-- **`α + Ω_ω = Ω_ω` whenever `α ≺ Ω_ω`.** -/
theorem add_OmegaW_of_lt {x : ThetaVNoteD} (h : x < OmegaW) : x + OmegaW = OmegaW := by
  rw [← omegaPow_OmegaW] at h ⊢
  exact add_omegaPow_of_lt h

end ThetaVNoteD

namespace IDw

open LO LO.FirstOrder

/-! ### The rank -/

section Rank

/-- The rank of a stage index: `Ω_{s.lvl} + ω · s.val`. -/
def atomRkStage (s : Stage) : ThetaVNoteD := ThetaVNoteD.OmegaBelow s.lvl +
  ThetaVNoteD.omegaMul s.val

theorem atomRkStage_mk (k : ℕ) (a : StageAt k) :
    atomRkStage (⟨k, a⟩ : Stage) = ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul a.1 := rfl

/-- **The rank of a `Jlev ℓ` atom**: `Ω_k + 1` at `ℓ = ↑k` (`k = 0` included: `Ω_0 + 1 = 1`, the
design's own aside), `Ω_ω` at `ℓ = ⊤`. -/
def atomRkJlev : WithTop ℕ → ThetaVNoteD
  | ⊤ => ThetaVNoteD.OmegaW
  | (k : ℕ) => ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow k)

@[simp] theorem atomRkJlev_top : atomRkJlev (⊤ : WithTop ℕ) = ThetaVNoteD.OmegaW := rfl

@[simp] theorem atomRkJlev_coe (k : ℕ) :
    atomRkJlev (k : WithTop ℕ) = ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow k) := rfl

/-- The rank of a relation symbol. -/
def atomRk : {k : ℕ} → LIinfW.Rel k → ThetaVNoteD
  | _, Sum.inl _ => ThetaVNoteD.zero
  | _, Sum.inr IInfRelW.X => ThetaVNoteD.zero
  | _, Sum.inr (IInfRelW.stage s) => atomRkStage s
  | _, Sum.inr (IInfRelW.jlev ℓ) => atomRkJlev ℓ

theorem atomRk_stage (s : Stage) :
    atomRk (Sum.inr (IInfRelW.stage s) : LIinfW.Rel 1) = atomRkStage s := rfl

theorem atomRk_jlev (ℓ : WithTop ℕ) :
    atomRk (Sum.inr (IInfRelW.jlev ℓ) : LIinfW.Rel 2) = atomRkJlev ℓ := rfl

/-- The structural recursion behind `rk`. -/
def rkRec {ξ : Type*} : {m : ℕ} → Semiformula LIinfW ξ m → ThetaVNoteD
  | _, .verum => ThetaVNoteD.zero
  | _, .falsum => ThetaVNoteD.zero
  | _, .rel r _ => atomRk r
  | _, .nrel r _ => atomRk r
  | _, .and φ ψ => ThetaVNoteD.succ (max (rkRec φ) (rkRec ψ))
  | _, .or φ ψ => ThetaVNoteD.succ (max (rkRec φ) (rkRec ψ))
  | _, .all φ => ThetaVNoteD.succ (rkRec φ)
  | _, .exs φ => ThetaVNoteD.succ (rkRec φ)

/-- **The rank** `rk(φ)`, `IDw` read for the design's §3.1 ranks paragraph. -/
irreducible_def rk {ξ : Type*} {m : ℕ} (φ : Semiformula LIinfW ξ m) : ThetaVNoteD := rkRec φ

section Equations

variable {ξ : Type*} {m : ℕ}

@[simp] theorem rk_verum : rk (⊤ : Semiformula LIinfW ξ m) = ThetaVNoteD.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_falsum : rk (⊥ : Semiformula LIinfW ξ m) = ThetaVNoteD.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_rel {k : ℕ} (r : LIinfW.Rel k) (v : Fin k → Semiterm LIinfW ξ m) :
    rk (Semiformula.rel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_nrel {k : ℕ} (r : LIinfW.Rel k) (v : Fin k → Semiterm LIinfW ξ m) :
    rk (Semiformula.nrel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_and (φ ψ : Semiformula LIinfW ξ m) :
    rk (φ ⋏ ψ) = ThetaVNoteD.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_or (φ ψ : Semiformula LIinfW ξ m) :
    rk (φ ⋎ ψ) = ThetaVNoteD.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_all (φ : Semiformula LIinfW ξ (m + 1)) :
    rk (∀¹ φ) = ThetaVNoteD.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

@[simp] theorem rk_exs (φ : Semiformula LIinfW ξ (m + 1)) :
    rk (∃¹ φ) = ThetaVNoteD.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

/-- `rk(I_k^{≺a} t) = Ω_k + ω · a`. -/
@[simp] theorem rk_stageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    rk (stageAt s t) = atomRkStage s := rk_rel _ _

/-- `rk(¬I_k^{≺a} t) = Ω_k + ω · a`. -/
@[simp] theorem rk_nstageAt (s : Stage) (t : Semiterm LIinfW ξ m) :
    rk (nstageAt s t) = atomRkStage s := rk_nrel _ _

/-- **`rk(I_k t) = Ω_{k+1}`.** -/
@[simp] theorem rk_IOmegaAt (k : ℕ) (t : Semiterm LIinfW ξ m) :
    rk (IOmegaAt k t) = ThetaVNoteD.Omega k := by
  rw [IOmegaAt, rk_stageAt]
  show ThetaVNoteD.OmegaBelow (Stage.top k).lvl + ThetaVNoteD.omegaMul (Stage.top k).val = _
  rw [Stage.lvl_top, Stage.val_top, ThetaVNoteD.omegaMul_Omega _,
    ThetaVNoteD.add_Omega_of_lt (ThetaVNoteD.OmegaBelow_lt_Omega k)]

@[simp] theorem rk_XinfAt (t : Semiterm LIinfW ξ m) : rk (XinfAt t) = ThetaVNoteD.zero :=
  rk_rel _ _

/-- **`rk(Jlev ℓ (s,t)) = Ω_k + 1` at `ℓ = ↑k`, `Ω_ω` at `ℓ = ⊤`.** -/
@[simp] theorem rk_jlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    rk (jlevAt ℓ s t) = atomRkJlev ℓ := rk_rel _ _

@[simp] theorem rk_njlevAt (ℓ : WithTop ℕ) (s t : Semiterm LIinfW ξ m) :
    rk (njlevAt ℓ s t) = atomRkJlev ℓ := rk_nrel _ _

/-- `rk(Jlev ⊤ (s,t)) = Ω_ω`, spelled out. -/
theorem rk_jlevAt_top (s t : Semiterm LIinfW ξ m) : rk (jlevAt ⊤ s t) = ThetaVNoteD.OmegaW :=
  rk_jlevAt ⊤ s t

theorem rk_njlevAt_top (s t : Semiterm LIinfW ξ m) : rk (njlevAt ⊤ s t) = ThetaVNoteD.OmegaW :=
  rk_njlevAt ⊤ s t

end Equations

/-! ### Negation and substitution -/

section Basic

variable {ξ : Type*} {m : ℕ}

/-- **`rk(¬φ) = rk(φ)`.** -/
@[simp] theorem rk_neg (φ : Semiformula LIinfW ξ m) : rk (∼φ) = rk φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The rank does not see terms**: it is invariant under every rewriting. -/
@[simp] theorem rk_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew LIinfW ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula LIinfW ξ₁ m₁) : rk (ω ▹ φ) = rk φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, rk_rel, rk_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, rk_nrel, rk_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem rk_subst (φ : Semiformula LIinfW ξ 1) (t : Semiterm LIinfW ξ m) :
    rk (φ/[t]) = rk φ := rk_rew _ φ

@[simp] theorem rk_subst2 (φ : Semiformula LIinfW ξ 2) (t u : Semiterm LIinfW ξ m) :
    rk (φ/[t, u]) = rk φ := rk_rew _ φ

theorem rk_subst_lt_all (φ : Semiformula LIinfW ξ 1) (t : Semiterm LIinfW ξ 0) :
    rk (φ/[t]) < rk (∀¹ φ) := by
  rw [rk_subst, rk_all]; exact ThetaVNoteD.lt_succ _

theorem rk_subst_lt_exs (φ : Semiformula LIinfW ξ 1) (t : Semiterm LIinfW ξ 0) :
    rk (φ/[t]) < rk (∃¹ φ) := by
  rw [rk_subst, rk_exs]; exact ThetaVNoteD.lt_succ _

theorem rk_lt_all (φ : Semiformula LIinfW ξ (m + 1)) : rk φ < rk (∀¹ φ) := by
  rw [rk_all]; exact ThetaVNoteD.lt_succ _

theorem rk_lt_exs (φ : Semiformula LIinfW ξ (m + 1)) : rk φ < rk (∃¹ φ) := by
  rw [rk_exs]; exact ThetaVNoteD.lt_succ _

theorem rk_left_lt_and (φ ψ : Semiformula LIinfW ξ m) : rk φ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaVNoteD.lt_succ _)

theorem rk_right_lt_and (φ ψ : Semiformula LIinfW ξ m) : rk ψ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaVNoteD.lt_succ _)

theorem rk_left_lt_or (φ ψ : Semiformula LIinfW ξ m) : rk φ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaVNoteD.lt_succ _)

theorem rk_right_lt_or (φ ψ : Semiformula LIinfW ξ m) : rk ψ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaVNoteD.lt_succ _)

end Basic

/-! ### The finite-part bound and the stage rank drop

**Deviation from `IDn.Rank`, flagged.** `IDn.rk_le_add_ofNat`'s generic finite-part bound
(`rk φ ≤ T ⊕ p` whenever every *stage* parameter of `φ` has `atomRkStage ≤ T`) does **not** port
honestly to `IDw`: `params (Jlev …) = ∅` (`IDw.Language`), so the hypothesis says nothing about
any `Jlev` atom `φ` may contain, yet a bare `Jlev ⊤` atom has rank `OmegaW`, unboundable by any
finite-complexity `T ⊕ p`. Stating the naive port would be *false*, not merely unneeded, so it is
not stated at all. What is actually needed downstream (`rk_unfold_le`, the bound the design's
§3.1 remark computes as "`max(Ω_k + 1, Ω_k + ω·g) + finite`") is proved directly instead, by a
bespoke induction on the *schema* `A` (`rk_lMap_formHomAt_le`) that tracks `formHomAt`'s two
*known* atom images (`P ↦ stage ⟨k,g⟩`, `Q ↦ jlev k`) at once, rather than trying to reconstruct
them from `params`. The `max` becomes a single uniform `+ 1` slack folded into the complexity
bound (`A.complexity + 1` in place of `A.complexity`): a `Jlev k` leaf's own rank `Ω_k + 1` is
always `≤ (Ω_k + ω·g) ⊕ 1`, unconditionally on `g` (`OmegaBelow k ≤ OmegaBelow k + omegaMul g.1`,
then `succ`-monotone), so the one extra finite step suffices in every case, and the downstream
comparison against `Ω_k + ω·a'` (`add_omegaMul_nadd_ofNat_lt`, `g ≺ a'`) already tolerates *any*
finite offset — no case split on `g`/`a'` positivity is needed after all. -/

section Bound

variable {ξ : Type*} {m : ℕ}

/-- **`rk` of `formHomAt k g`'s image is bounded**, for a schema at any arity `n`: a direct
structural induction on `A`, tracking both atoms `formHomAt` can produce — `P ↦ stage ⟨k,g⟩`
(rank `Ω_k + ω·g`) and `Q ↦ jlev k` (rank `Ω_k + 1`) — at once, since neither `params` nor
`SigmaW`-style bookkeeping alone sees both. -/
theorem rk_lMap_formHomAt_le (k : ℕ) (g : StageAt k) :
    ∀ {n : ℕ} (A : Semiformula LForm Empty n),
      rk (Semiformula.lMap (formHomAt k g) A) ≤
        (ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul g.1) +
          ThetaVNoteD.ofNat (A.complexity + 1) := by
  intro n A
  induction A using Semiformula.rec' with
  | hverum =>
    rw [LogicalConnective.HomClass.map_top, rk_verum]; exact ThetaVNoteD.zero_le' _
  | hfalsum =>
    rw [LogicalConnective.HomClass.map_bot, rk_falsum]; exact ThetaVNoteD.zero_le' _
  | hrel r v =>
    show rk (Semiformula.rel (formRelAt k g r)
      (fun i => Semiterm.lMap (formHomAt k g) (v i))) ≤ _
    rw [rk_rel]
    rcases r with r | r
    · exact ThetaVNoteD.zero_le' _
    · cases r with
      | P =>
        show atomRkStage (⟨k, g⟩ : Stage) ≤ _
        rw [atomRkStage_mk]
        exact ThetaVNoteD.le_add_right _ _
      | Q =>
        show atomRkJlev (k : WithTop ℕ) ≤ _
        rw [atomRkJlev_coe, ← ThetaVNoteD.add_one_eq_succ, ThetaVNoteD.add_assoc]
        refine ThetaVNoteD.add_le_add_left _ ?_
        calc ThetaVNoteD.one = ThetaVNoteD.ofNat 1 := ThetaVNoteD.ofNat_one.symm
          _ ≤ ThetaVNoteD.ofNat (_ + 1) := ThetaVNoteD.ofNat_le_ofNat (Nat.le_add_left 1 _)
          _ ≤ ThetaVNoteD.omegaMul g.1 + ThetaVNoteD.ofNat (_ + 1) := ThetaVNoteD.le_add_left _ _
  | hnrel r v =>
    show rk (Semiformula.nrel (formRelAt k g r)
      (fun i => Semiterm.lMap (formHomAt k g) (v i))) ≤ _
    rw [rk_nrel]
    rcases r with r | r
    · exact ThetaVNoteD.zero_le' _
    · cases r with
      | P =>
        show atomRkStage (⟨k, g⟩ : Stage) ≤ _
        rw [atomRkStage_mk]
        exact ThetaVNoteD.le_add_right _ _
      | Q =>
        show atomRkJlev (k : WithTop ℕ) ≤ _
        rw [atomRkJlev_coe, ← ThetaVNoteD.add_one_eq_succ, ThetaVNoteD.add_assoc]
        refine ThetaVNoteD.add_le_add_left _ ?_
        calc ThetaVNoteD.one = ThetaVNoteD.ofNat 1 := ThetaVNoteD.ofNat_one.symm
          _ ≤ ThetaVNoteD.ofNat (_ + 1) := ThetaVNoteD.ofNat_le_ofNat (Nat.le_add_left 1 _)
          _ ≤ ThetaVNoteD.omegaMul g.1 + ThetaVNoteD.ofNat (_ + 1) := ThetaVNoteD.le_add_left _ _
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, rk_and, Semiformula.complexity_and,
      ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (Nat.add_le_add_right (le_max_left _ _) 1)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (Nat.add_le_add_right (le_max_right _ _) 1)))
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, rk_or, Semiformula.complexity_or,
      ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (Nat.add_le_add_right (le_max_left _ _) 1)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _
        (ThetaVNoteD.ofNat_le_ofNat (Nat.add_le_add_right (le_max_right _ _) 1)))
  | hall φ ih =>
    rw [Semiformula.lMap_all, rk_all, Semiformula.complexity_all, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih
  | hexs φ ih =>
    rw [Semiformula.lMap_exs, rk_exs, Semiformula.complexity_exs, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih

/-- **`rk(unfoldW A k g t) ⪯ (Ω_k + ω · g) ⊕ (p+1)`**, `p` the complexity of the *schema* `A` —
via the exact equality `rk (unfoldW A k g t) = rk (lMap (formHomAt k g) A)` (`rk` sees neither the
`Rewriting.emb` cast nor the `/[t,k̄]` substitution, `rk_rew`/`rk_subst2`), then
`rk_lMap_formHomAt_le`. -/
theorem rk_unfold_le (A : FormJ) {k : ℕ} (g : StageAt k) (t : Semiterm LIinfW ξ m) :
    rk (unfoldW A k g t) ≤
      (ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul g.1) +
        ThetaVNoteD.ofNat (A.complexity + 1) := by
  have heq : rk (unfoldW A k g t) = rk (formAtW A k g) := by
    unfold unfoldW
    rw [rk_subst2, rk_rew]
  rw [heq]
  exact rk_lMap_formHomAt_le k g A

/-- **The stage case**: `rk(unfoldW A k g t) ≺ rk(I_k^{≺a'} s)` for `g ≺ a'` at the *same* level
`k` — the rank drop of the infinite disjunction `I_k^{≺a'} s ≃ ⋁_{g≺a'} A_k(s, I_k^{≺g})` and of
the dual conjunction (design §3.1: "`rk(unfoldW A k g t) ≺ Ω_k + ω·a` for `g ≺ a` still holds",
`max(Ω_k+1, Ω_k+ω·g) + finite` folded into the single `+ (p+1)` slack of `rk_unfold_le` above —
`add_omegaMul_nadd_ofNat_lt` tolerates *any* finite offset on the smaller side, so the extra `+1`
costs nothing here). -/
theorem rk_unfold_lt_stageAt (A : FormJ) {k : ℕ} {g a' : StageAt k} (h : g.1 < a'.1)
    (t s : Semiterm LIinfW ξ m) : rk (unfoldW A k g t) < rk (stageAt (⟨k, a'⟩ : Stage) s) := by
  rw [rk_stageAt]
  show rk (unfoldW A k g t) < ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul a'.1
  have hbound := rk_unfold_le A g t
  refine lt_of_le_of_lt hbound ?_
  rw [ThetaVNoteD.add_ofNat_eq_nadd_ofNat]
  exact ThetaVNoteD.add_omegaMul_nadd_ofNat_lt _ h _

theorem rk_unfold_lt_nstageAt (A : FormJ) {k : ℕ} {g a' : StageAt k} (h : g.1 < a'.1)
    (t s : Semiterm LIinfW ξ m) : rk (unfoldW A k g t) < rk (nstageAt (⟨k, a'⟩ : Stage) s) := by
  rw [rk_nstageAt, ← rk_stageAt (⟨k, a'⟩ : Stage) s]
  exact rk_unfold_lt_stageAt A h t s

/-- A countable (`≺` top) stage of level `k` unfolds to a formula of rank `≺ Ω_{k+1}`. -/
theorem rk_unfold_lt_Omega (A : FormJ) {k : ℕ} {g : StageAt k} (hg : g.1 < ThetaVNoteD.Omega k)
    (t : Semiterm LIinfW ξ m) : rk (unfoldW A k g t) < ThetaVNoteD.Omega k := by
  have h := rk_unfold_lt_stageAt A (a' := StageAt.top k) hg t t
  rw [show (⟨k, StageAt.top k⟩ : Stage) = Stage.top k from rfl] at h
  rwa [← IOmegaAt_eq, rk_IOmegaAt] at h

end Bound

/-! ### Rank `Ω_{k+1}` and the class `Σ(Ω_{k+1})` -/

section Omega

variable {ξ : Type*} {m : ℕ}

theorem stage_eq_top_iff_of_lvl_eq {s : Stage} {k : ℕ} (h : s.lvl = k) :
    s = Stage.top k ↔ s.val = ThetaVNoteD.Omega k := by
  obtain ⟨j, a⟩ := s
  have h' : j = k := h
  subst h'
  rw [Stage.mk_eq_top_iff]
  exact Subtype.ext_iff

/-- **`Ω_j + ω · a ≺ Ω_{k+1}` iff `j ≤ k` and `(j, a) ≠ (k, Ω_{k+1})`** — this is exactly
`NrelSigmaW k` read on the stage index. -/
theorem atomRkStage_lt_Omega_iff {k : ℕ} {s : Stage} :
    atomRkStage s < ThetaVNoteD.Omega k ↔ s.lvl ≤ k ∧ s ≠ Stage.top k := by
  show ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val < ThetaVNoteD.Omega k ↔ _
  rcases lt_trichotomy s.lvl k with hlt | heq | hgt
  · have hval_le : ThetaVNoteD.omegaMul s.val ≤ ThetaVNoteD.Omega s.lvl := by
      rcases lt_or_eq_of_le s.le with h | h
      · exact le_of_lt (ThetaVNoteD.omegaMul_lt_prin trivial h)
      · rw [h, ThetaVNoteD.omegaMul_Omega _]
    have hsum_le : ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val ≤
        ThetaVNoteD.Omega s.lvl := by
      calc ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val
          ≤ ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.Omega s.lvl :=
            ThetaVNoteD.add_le_add_left _ hval_le
        _ = ThetaVNoteD.Omega s.lvl := ThetaVNoteD.add_Omega_of_lt
            (ThetaVNoteD.OmegaBelow_lt_Omega s.lvl)
    have hlhs : ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val <
        ThetaVNoteD.Omega k :=
      lt_of_le_of_lt hsum_le (ThetaVNoteD.Omega_lt_Omega_iff.mpr hlt)
    have hne : s ≠ Stage.top k := Stage.ne_top_of_lvl_ne (Nat.ne_of_lt hlt)
    exact ⟨fun _ => ⟨le_of_lt hlt, hne⟩, fun _ => hlhs⟩
  · have homega_eq : ThetaVNoteD.Omega s.lvl = ThetaVNoteD.Omega k := by rw [heq]
    by_cases hval : s.val = ThetaVNoteD.Omega k
    · have hstop : s = Stage.top k := (stage_eq_top_iff_of_lvl_eq heq).mpr hval
      have heqrk : ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val =
          ThetaVNoteD.Omega k := by
        rw [hval, ThetaVNoteD.omegaMul_Omega _, heq, ThetaVNoteD.add_Omega_of_lt
          (ThetaVNoteD.OmegaBelow_lt_Omega k)]
      constructor
      · intro h; rw [heqrk] at h; exact absurd h (lt_irrefl _)
      · rintro ⟨-, hne'⟩; exact absurd hstop hne'
    · have hval' : s.val ≠ ThetaVNoteD.Omega s.lvl := by rw [homega_eq]; exact hval
      have hval_lt' : s.val < ThetaVNoteD.Omega s.lvl := lt_of_le_of_ne s.le hval'
      have h2 : ThetaVNoteD.OmegaBelow s.lvl + ThetaVNoteD.omegaMul s.val <
          ThetaVNoteD.Omega k := by
        rw [← homega_eq]
        exact ThetaVNoteD.add_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_Omega s.lvl)
          (ThetaVNoteD.omegaMul_lt_prin trivial hval_lt')
      have hne : s ≠ Stage.top k := fun e =>
        hval ((stage_eq_top_iff_of_lvl_eq heq).mp e)
      exact ⟨fun _ => ⟨le_of_eq heq, hne⟩, fun _ => h2⟩
  · have hge : ThetaVNoteD.Omega k ≤ ThetaVNoteD.OmegaBelow s.lvl +
        ThetaVNoteD.omegaMul s.val :=
      le_trans (ThetaVNoteD.Omega_le_OmegaBelow_of_lt hgt) (ThetaVNoteD.le_add_right _ _)
    constructor
    · intro h; exact absurd h (not_lt_of_ge hge)
    · rintro ⟨h1, -⟩; exact absurd h1 (not_le_of_gt hgt)

/-- **`atomRkJlev ℓ ≺ Ω_{k+1}` iff `ℓ ≤ ↑k`** — this is exactly `NrelSigmaW k`/`RelSigmaW k` read
on a `Jlev` index (both polarities coincide, unlike the stage case, since `Jlev` has no "own top"
to exclude). -/
theorem atomRkJlev_lt_Omega_iff {k : ℕ} {ℓ : WithTop ℕ} :
    atomRkJlev ℓ < ThetaVNoteD.Omega k ↔ ℓ ≤ (k : WithTop ℕ) := by
  induction ℓ using WithTop.recTopCoe with
  | top =>
    rw [atomRkJlev_top]
    constructor
    · intro h
      exact absurd (lt_trans (ThetaVNoteD.Omega_lt_OmegaW k) h) (lt_irrefl _)
    · intro h
      simp at h
  | coe j =>
    have core : ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) < ThetaVNoteD.Omega k ↔ j ≤ k := by
      constructor
      · intro h
        by_contra hjk
        push Not at hjk
        have h1 : ThetaVNoteD.Omega k ≤ ThetaVNoteD.OmegaBelow j :=
          ThetaVNoteD.Omega_le_OmegaBelow_of_lt hjk
        have h2 : ThetaVNoteD.Omega k < ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) :=
          lt_of_le_of_lt h1 (ThetaVNoteD.lt_succ _)
        exact absurd (lt_trans h h2) (lt_irrefl _)
      · intro h
        rcases lt_or_eq_of_le h with hjk | rfl
        · have h1 : ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) ≤ ThetaVNoteD.Omega j :=
            le_of_lt (ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_Omega j))
          have h2 : ThetaVNoteD.Omega j ≤ ThetaVNoteD.OmegaBelow k :=
            ThetaVNoteD.Omega_le_OmegaBelow_of_lt hjk
          exact lt_of_le_of_lt (h1.trans h2) (ThetaVNoteD.OmegaBelow_lt_Omega k)
        · exact ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_Omega j)
    exact core.trans WithTop.coe_le_coe.symm

/-- **A formula of rank `≺ Ω_{k+1}` is `Σ(Ω_{k+1})`, and so is its negation, and conversely.**
The `IDw`-honest replacement for `IDn.rk_lt_Omega_iff`'s pure-`params` characterization: `params`
is blind to `Jlev` (`params (Jlev …) = ∅`, `IDw.Language`), so a bound on `params φ` alone no
longer bounds `rk φ` (a bare `Jlev ⊤` atom has `params = ∅` but `rk = OmegaW`, far above every
`Omega k`) — the honest per-level statement compares `rk` directly against membership in
`SigmaW k`, the class that was built for exactly this purpose, rather than reconstructing it from
`params`. Both directions are genuine: (→) by structural induction, using `atomRkStage_lt_Omega_
iff`/`atomRkJlev_lt_Omega_iff` at the atoms; (←) is the converse computation at the same atoms,
which happens to be exactly as tight (`Jlev`'s `RelSigmaW`/`NrelSigmaW k` agree, so the atom case
needs no extra polarity bookkeeping there, unlike the stage case). -/
theorem rk_lt_Omega_iff {k : ℕ} {φ : Semiformula LIinfW ξ m} :
    rk φ < ThetaVNoteD.Omega k ↔ SigmaW k φ ∧ SigmaW k (∼φ) := by
  induction φ using Semiformula.rec' with
  | hverum => simp [ThetaVNoteD.zero_lt_Omega]
  | hfalsum => simp [ThetaVNoteD.zero_lt_Omega]
  | hrel r v =>
    rw [rk_rel]
    show atomRk r < ThetaVNoteD.Omega k ↔
      SigmaW k (Semiformula.rel r v) ∧ SigmaW k (∼(Semiformula.rel r v))
    rw [Semiformula.neg_rel, sigmaW_rel, sigmaW_nrel]
    rcases r with r | r
    · simp [atomRk, RelSigmaW, NrelSigmaW, ThetaVNoteD.zero_lt_Omega]
    · cases r with
      | X => simp [atomRk, RelSigmaW, NrelSigmaW, ThetaVNoteD.zero_lt_Omega]
      | stage s =>
        show atomRkStage s < ThetaVNoteD.Omega k ↔ s.lvl ≤ k ∧ (s.lvl ≤ k ∧ s ≠ Stage.top k)
        rw [atomRkStage_lt_Omega_iff]
        exact ⟨fun h => ⟨h.1, h⟩, fun h => h.2⟩
      | jlev ℓ =>
        show atomRkJlev ℓ < ThetaVNoteD.Omega k ↔
          ℓ ≤ (k : WithTop ℕ) ∧ ℓ ≤ (k : WithTop ℕ)
        rw [atomRkJlev_lt_Omega_iff]
        exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | hnrel r v =>
    rw [rk_nrel]
    show atomRk r < ThetaVNoteD.Omega k ↔
      SigmaW k (Semiformula.nrel r v) ∧ SigmaW k (∼(Semiformula.nrel r v))
    rw [Semiformula.neg_nrel, sigmaW_nrel, sigmaW_rel]
    rcases r with r | r
    · simp [atomRk, RelSigmaW, NrelSigmaW, ThetaVNoteD.zero_lt_Omega]
    · cases r with
      | X => simp [atomRk, RelSigmaW, NrelSigmaW, ThetaVNoteD.zero_lt_Omega]
      | stage s =>
        show atomRkStage s < ThetaVNoteD.Omega k ↔ (s.lvl ≤ k ∧ s ≠ Stage.top k) ∧ s.lvl ≤ k
        rw [atomRkStage_lt_Omega_iff]
        exact ⟨fun h => ⟨h, h.1⟩, fun h => h.1⟩
      | jlev ℓ =>
        show atomRkJlev ℓ < ThetaVNoteD.Omega k ↔
          ℓ ≤ (k : WithTop ℕ) ∧ ℓ ≤ (k : WithTop ℕ)
        rw [atomRkJlev_lt_Omega_iff]
        exact ⟨fun h => ⟨h, h⟩, fun h => h.1⟩
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.Omega k) trivial, max_lt_iff,
      ihφ, ihψ]
    show _ ↔ SigmaW k (φ ⋏ ψ) ∧ SigmaW k (∼φ ⋎ ∼ψ)
    rw [sigmaW_and, sigmaW_or]
    tauto
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.Omega k) trivial, max_lt_iff,
      ihφ, ihψ]
    show _ ↔ SigmaW k (φ ⋎ ψ) ∧ SigmaW k (∼φ ⋏ ∼ψ)
    rw [sigmaW_or, sigmaW_and]
    tauto
  | hall φ ih =>
    rw [rk_all, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.Omega k) trivial, ih]
    show _ ↔ SigmaW k (∀¹ φ) ∧ SigmaW k (∃¹ (∼φ))
    rw [sigmaW_all, sigmaW_exs]
  | hexs φ ih =>
    rw [rk_exs, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.Omega k) trivial, ih]
    show _ ↔ SigmaW k (∃¹ φ) ∧ SigmaW k (∀¹ (∼φ))
    rw [sigmaW_exs, sigmaW_all]

/-- **A formula of rank `≺ Ω_{k+1}` is `Σ(Ω_{k+1})`, and so is its negation** — the one-directional
corollary, named to match `IDn.sigmaW_of_rk_lt_Omega`. -/
theorem sigmaW_of_rk_lt_Omega {k : ℕ} {φ : Semiformula LIinfW ξ m}
    (h : rk φ < ThetaVNoteD.Omega k) : SigmaW k φ ∧ SigmaW k (∼φ) := rk_lt_Omega_iff.mp h

end Omega

/-! ### Bounding: `capAt` does not raise the rank -/

section Cap

variable {ξ : Type*} {m : ℕ}

theorem atomRkStage_top (k : ℕ) : atomRkStage (Stage.top k) = ThetaVNoteD.Omega k := by
  show ThetaVNoteD.OmegaBelow (Stage.top k).lvl + ThetaVNoteD.omegaMul (Stage.top k).val = _
  rw [Stage.lvl_top, Stage.val_top, ThetaVNoteD.omegaMul_Omega _,
    ThetaVNoteD.add_Omega_of_lt (ThetaVNoteD.OmegaBelow_lt_Omega k)]

/-- `capAt`'s effect on a relation symbol never raises its atom rank: the only symbol it ever
changes is the top stage of level `k`, replaced by `⟨k,b⟩` (rank `≤ Ω_{k+1}`, `atomRkStage_mk_le_
Omega`); every `Jlev` symbol is untouched (`capRelAt`'s `jlev` clause is the identity, design
§3.1), so its case is `le_refl` outright. -/
theorem atomRkStage_mk_le_Omega (k : ℕ) (b : StageAt k) :
    atomRkStage (⟨k, b⟩ : Stage) ≤ ThetaVNoteD.Omega k := by
  rw [atomRkStage_mk]
  calc ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul b.1
      ≤ ThetaVNoteD.OmegaBelow k + ThetaVNoteD.omegaMul (ThetaVNoteD.Omega k) :=
        ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.omegaMul_le_omegaMul b.2)
    _ = ThetaVNoteD.OmegaBelow k + ThetaVNoteD.Omega k := by rw [ThetaVNoteD.omegaMul_Omega _]
    _ = ThetaVNoteD.Omega k := ThetaVNoteD.add_Omega_of_lt (ThetaVNoteD.OmegaBelow_lt_Omega k)

theorem atomRk_capRelAt_le (k : ℕ) (b : StageAt k) :
    ∀ {j : ℕ} (r : LIinfW.Rel j), atomRk (capRelAt k b r) ≤ atomRk r
  | _, Sum.inl _ => le_refl _
  | _, Sum.inr IInfRelW.X => le_refl _
  | _, Sum.inr (IInfRelW.stage s) => by
    rw [capRelAt_stage]
    split_ifs with h
    · rw [atomRk_stage, atomRk_stage, h, atomRkStage_top]
      exact atomRkStage_mk_le_Omega k b
    · exact le_refl _
  | _, Sum.inr (IInfRelW.jlev ℓ) => le_refl _

/-- **Bounding at level `k` does not raise the rank**: `rk(φ^β) ⪯ rk(φ)`. -/
theorem rk_capAt_le (k : ℕ) (b : StageAt k) (φ : Semiformula LIinfW ξ m) :
    rk (capAt k b φ) ≤ rk φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact le_refl _
  | hfalsum => exact le_refl _
  | hrel r v => rw [capAt_rel, rk_rel, rk_rel]; exact atomRk_capRelAt_le k b r
  | hnrel r v => rw [capAt_nrel, rk_nrel, rk_nrel]; exact atomRk_capRelAt_le k b r
  | hand φ ψ ihφ ihψ =>
    rw [capAt_and, rk_and, rk_and]; exact ThetaVNoteD.succ_le_succ (max_le_max ihφ ihψ)
  | hor φ ψ ihφ ihψ =>
    rw [capAt_or, rk_or, rk_or]; exact ThetaVNoteD.succ_le_succ (max_le_max ihφ ihψ)
  | hall φ ih => rw [capAt_all, rk_all, rk_all]; exact ThetaVNoteD.succ_le_succ ih
  | hexs φ ih => rw [capAt_exs, rk_exs, rk_exs]; exact ThetaVNoteD.succ_le_succ ih

end Cap

/-! ### The limit: rank `≺ Ω_ω` and the embedded `LXJ`-formulas -/

section Limit

variable {ξ : Type*} {m : ℕ}

/-- The relation symbols that keep a formula's rank away from `OmegaW`: every symbol except
`Jlev ⊤` (which, in *either* polarity, has atom rank exactly `OmegaW` — `atomRkJlev_top`, and
`rk_jlevAt`/`rk_njlevAt` do not distinguish polarity). -/
def relNoJlevTop : {k : ℕ} → LIinfW.Rel k → Prop
  | _, Sum.inl _ => True
  | _, Sum.inr IInfRelW.X => True
  | _, Sum.inr (IInfRelW.stage _) => True
  | _, Sum.inr (IInfRelW.jlev ℓ) => ℓ ≠ ⊤

/-- **No `Jlev ⊤` atom occurs in `φ`, either polarity** — the `Ω_ω`-analogue of `SigmaW k`'s role
in `rk_lt_Omega_iff`: every stage atom and every `Jlev k` (`k : ℕ`) atom is automatically `≺ Ω_ω`
regardless of level (`OmegaBelow_lt_OmegaW`, unconditional on `k`), so `Jlev ⊤` is the *only*
obstruction, and it is polarity-independent (unlike the per-level stage case), so — unlike
`SigmaW`/`rk_lt_Omega_iff` — no separate negation-pairing is needed: `NoJlevTop (∼φ) = NoJlevTop
φ` holds outright, by the very same recursion (`∼` swaps `rel`/`nrel` only, both landing on
`relNoJlevTop`). -/
def NoJlevTop {ξ : Type*} : {m : ℕ} → Semiformula LIinfW ξ m → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel r _ => relNoJlevTop r
  | _, .nrel r _ => relNoJlevTop r
  | _, .and φ ψ => NoJlevTop φ ∧ NoJlevTop ψ
  | _, .or φ ψ => NoJlevTop φ ∧ NoJlevTop ψ
  | _, .all φ => NoJlevTop φ
  | _, .exs φ => NoJlevTop φ

/-- **A formula has rank `≺ Ω_ω` iff it contains no `Jlev ⊤` atom** (design §3.1's "for formulas
without top-level `Jlev ⊤`"). -/
theorem rk_lt_OmegaW_iff {φ : Semiformula LIinfW ξ m} :
    rk φ < ThetaVNoteD.OmegaW ↔ NoJlevTop φ := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
  | hfalsum => rw [rk_falsum]; exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
  | hrel r v =>
    rw [rk_rel]
    show atomRk r < ThetaVNoteD.OmegaW ↔ relNoJlevTop r
    rcases r with r | r
    · exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
    · cases r with
      | X => exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
      | stage s =>
        refine iff_of_true ?_ trivial
        show atomRkStage s < ThetaVNoteD.OmegaW
        exact ThetaVNoteD.add_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW s.lvl)
          (lt_of_le_of_lt (ThetaVNoteD.omegaMul_le_omegaMul s.le)
            (by rw [ThetaVNoteD.omegaMul_Omega]; exact ThetaVNoteD.Omega_lt_OmegaW s.lvl))
      | jlev ℓ =>
        show atomRkJlev ℓ < ThetaVNoteD.OmegaW ↔ ℓ ≠ ⊤
        induction ℓ using WithTop.recTopCoe with
        | top =>
          rw [atomRkJlev_top]
          constructor
          · intro h; exact absurd h (lt_irrefl _)
          · intro h; exact absurd (rfl : (⊤ : WithTop ℕ) = ⊤) h
        | coe j =>
          show ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) < ThetaVNoteD.OmegaW ↔
            (j : WithTop ℕ) ≠ ⊤
          exact iff_of_true (ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW j))
            WithTop.coe_ne_top
  | hnrel r v =>
    rw [rk_nrel]
    show atomRk r < ThetaVNoteD.OmegaW ↔ relNoJlevTop r
    rcases r with r | r
    · exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
    · cases r with
      | X => exact iff_of_true ThetaVNoteD.zero_lt_OmegaW trivial
      | stage s =>
        refine iff_of_true ?_ trivial
        show atomRkStage s < ThetaVNoteD.OmegaW
        exact ThetaVNoteD.add_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW s.lvl)
          (lt_of_le_of_lt (ThetaVNoteD.omegaMul_le_omegaMul s.le)
            (by rw [ThetaVNoteD.omegaMul_Omega]; exact ThetaVNoteD.Omega_lt_OmegaW s.lvl))
      | jlev ℓ =>
        show atomRkJlev ℓ < ThetaVNoteD.OmegaW ↔ ℓ ≠ ⊤
        induction ℓ using WithTop.recTopCoe with
        | top =>
          rw [atomRkJlev_top]
          constructor
          · intro h; exact absurd h (lt_irrefl _)
          · intro h; exact absurd (rfl : (⊤ : WithTop ℕ) = ⊤) h
        | coe j =>
          show ThetaVNoteD.succ (ThetaVNoteD.OmegaBelow j) < ThetaVNoteD.OmegaW ↔
            (j : WithTop ℕ) ≠ ⊤
          exact iff_of_true (ThetaVNoteD.succ_lt_prin trivial (ThetaVNoteD.OmegaBelow_lt_OmegaW j))
            WithTop.coe_ne_top
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.OmegaW) trivial, max_lt_iff,
      ihφ, ihψ]
    rfl
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.OmegaW) trivial, max_lt_iff,
      ihφ, ihψ]
    rfl
  | hall φ ih =>
    rw [rk_all, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.OmegaW) trivial, ih]
    rfl
  | hexs φ ih =>
    rw [rk_exs, ThetaVNoteD.succ_lt_prin_iff (p := ThetaVNoteD.OmegaW) trivial, ih]
    rfl

theorem rk_lt_OmegaW {φ : Semiformula LIinfW ξ m} (h : NoJlevTop φ) :
    rk φ < ThetaVNoteD.OmegaW := rk_lt_OmegaW_iff.mpr h

/-- **The embedded `LXJ`-formulas**: `embedW`'s only new atom is `J ↦ Jlev ⊤` (rank exactly
`OmegaW`), `X ↦ X` (rank `0`) — direct structural induction on `φ`, mirroring `rk_lMap_formHomAt_
le` but simpler (only two atom cases, and the bound needs no `+1` slack: `OmegaW` itself, not a
finite successor of it, already dominates `0` with room to spare via a plain `≤`). -/
theorem rk_embed_le (φ : Semiformula LXJ ξ m) :
    rk (embed φ) ≤ ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat φ.complexity := by
  unfold embed
  induction φ using Semiformula.rec' with
  | hverum =>
    rw [LogicalConnective.HomClass.map_top, rk_verum]; exact ThetaVNoteD.zero_le' _
  | hfalsum =>
    rw [LogicalConnective.HomClass.map_bot, rk_falsum]; exact ThetaVNoteD.zero_le' _
  | hrel r v =>
    show rk (Semiformula.rel (embedRelW r) (fun i => Semiterm.lMap embedW (v i))) ≤ _
    rw [rk_rel]
    rcases r with r | r
    · exact ThetaVNoteD.zero_le' _
    · cases r with
      | X => exact ThetaVNoteD.zero_le' _
      | J =>
        show atomRkJlev (⊤ : WithTop ℕ) ≤ _
        rw [atomRkJlev_top]
        exact ThetaVNoteD.le_add_right _ _
  | hnrel r v =>
    show rk (Semiformula.nrel (embedRelW r) (fun i => Semiterm.lMap embedW (v i))) ≤ _
    rw [rk_nrel]
    rcases r with r | r
    · exact ThetaVNoteD.zero_le' _
    · cases r with
      | X => exact ThetaVNoteD.zero_le' _
      | J =>
        show atomRkJlev (⊤ : WithTop ℕ) ≤ _
        rw [atomRkJlev_top]
        exact ThetaVNoteD.le_add_right _ _
  | hand φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_and, rk_and, Semiformula.complexity_and,
      ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
    rw [LogicalConnective.HomClass.map_or, rk_or, Semiformula.complexity_or,
      ← ThetaVNoteD.succ_add_ofNat]
    refine ThetaVNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans ihφ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans ihψ (ThetaVNoteD.add_le_add_left _ (ThetaVNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hall φ ih =>
    rw [Semiformula.lMap_all, rk_all, Semiformula.complexity_all, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih
  | hexs φ ih =>
    rw [Semiformula.lMap_exs, rk_exs, Semiformula.complexity_exs, ← ThetaVNoteD.succ_add_ofNat]
    exact ThetaVNoteD.succ_le_succ ih

/-- **`rk (embedW φ) ≤ OmegaW + ofNat m`-type bound**, `params (embed φ) = ∅` (`IDw.params_embed`)
making it vacuously compatible with any level — restated with the `embed`/complexity names used
throughout this file. -/
theorem rk_embed_le_OmegaW_add_ofNat (φ : Semiformula LXJ ξ m) :
    rk (embed φ) ≤ ThetaVNoteD.OmegaW + ThetaVNoteD.ofNat φ.complexity := rk_embed_le φ

end Limit

end Rank

end IDw

end OrdinalAnalysis
