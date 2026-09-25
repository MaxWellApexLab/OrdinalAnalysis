/-
  The rank of the formulas of the infinitary language of `ID n`, one family of stage
  predicates per level.

  Source: A. Freund, arXiv:2204.09321, Definition 5.2 (as ported by `ID1/Rank.lean`):

      rk(I_k^{≺α} t) := rk(¬I_k^{≺α} t) := Ω_k + ω·α        (ordinal sum; `Ω_0 := 0`, so `k = 0`
                                                              gives ID₁'s `ω·α` back verbatim),
      rk(ψ₀ ∨ ψ₁) := rk(ψ₀ ∧ ψ₁)    := max{rk ψ₀, rk ψ₁} + 1,
      rk(∃x ψ)    := rk(∀x ψ)       := rk ψ + 1.

  `Ω_k` is `OmegaBelow k`, a helper defined below (`OmegaBelow 0 := 0`, `OmegaBelow (m+1) :=
  ThetaWNoteD.Omega m`, since `ThetaWNoteD.Omega m` denotes `Ω_{m+1}` — `ThetaW/Dom.lean`'s
  convention). `+` is the *ordinary* ordinal sum (`ThetaWNoteD.add`), not the natural sum used for
  `+ 1` in the connective/quantifier clauses (`ThetaWNoteD.succ`, `= · ⊕ ThetaWNoteD.one`) — the two
  coincide on `ofNat n` on the right (`add_ofNat_eq_nadd_ofNat` below), which is what lets the
  finite-part bound (`rk_le_add_ofNat`) carry over.

  **The laws proved, one per level `k` where the class in question is level-`k`-relative**
  (mirroring `ID1/Rank.lean`'s list):

    * `rk (∼φ) = rk φ`, and the rank does not see terms (`rk_rew`, `rk_subst`), so an instance of a
      quantified formula, and each conjunct/disjunct, has smaller rank;
    * **Exercise 5.3, stage case, at level `k`**: `rk(A_k(t, I_k^{≺a})) ≺ Ω_k + ω·a' = rk(I_k^{≺a'}
      s)` for `a ≺ a'` at the same level `k` (`rk_unfold_lt_stageAt`), via the finite-part bound
      `rk(A_k(t, I_k^{≺a})) ⪯ (Ω_k + ω·a) ⊕ p` (`rk_unfold_le`, `p` the complexity) and
      `(Ω_k + ω·a) ⊕ p ≺ Ω_k + ω·a'` (`add_omegaMul_nadd_ofNat_lt`, ported from `Theta`'s
      `omegaMul_nadd_ofNat_lt` with the extra, order-preserved `Ω_k +` prefix);
    * `rk(I_k^{≺a} t) ≺ Ω_{k+1}` for `a ≺ Ω_{k+1}`, and `rk(I_k t) = Ω_{k+1}`;
    * **a formula of rank `≺ Ω_{k+1}` has every stage parameter of level `≤ k` and `≠ Stage.top k`**
      — the per-level `rk_lt_Omega_iff` — hence it and its negation are `Σ(Ω_{k+1})`
      (`sigmaW_of_rk_lt_Omega`);
    * **Exercise 5.5(e)**: `rk φ` lies in every set containing `0` and the level-`k`-atom-ranks of
      the parameters of `φ` and closed under `+ 1` (`rk_mem_of_closed`);
    * bounding at level `k` does not raise the rank (`rk_cap_le`).

  With `ThetaWNoteD`'s `OrdinalNotation` instance (`ThetaW/Instance.lean`, `WellFoundedLT` already
  registered), the successor of Definition 5.2 is the generic `OrdinalNotation.succ`
  (`rk_and_succ`, …), so the generic calculus's height/rank bookkeeping applies verbatim.
-/
import OrdinalAnalysis.IDn.Language
import OrdinalAnalysis.Ordinal.ThetaW.Instance

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### Term-level facts needed for the finite-part bound (ported from `ID1/Rank.lean`, with
`ThetaTerm`/`ThetaNote` replaced by `ThetaWTerm`/`ThetaWNoteD`; none of this needs a level). -/

namespace ThetaWTerm

theorem addL_zero_ne_nil : ∀ L : List ThetaWTerm, addL [sum []] L ≠ []
  | [] => by simp [addL]
  | y :: ys => by rw [addL_cons]; simp

/-- `0 ≺ 1 + e`. -/
theorem nil_lt_onePlus (e : ThetaWTerm) : sum [] < onePlus e := by
  apply nil_lt_of_ne
  intro h
  exact addL_zero_ne_nil (toList e) (ofList_injective (h.trans ofList_nil.symm))

/-- If `xs` is lexicographically below `ys`, then appending zero exponents to `xs` after raising
every exponent by `1 +` keeps it below `ys` raised the same way. -/
theorem sum_map_onePlus_append_lt {zs : List ThetaWTerm} (hz : ∀ z ∈ zs, z = sum []) :
    ∀ {xs ys : List ThetaWTerm}, List.Lex (· < ·) xs ys → (∀ x ∈ xs, NF x) →
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

end ThetaWTerm

namespace ThetaWNoteD

theorem zero_le' (x : ThetaWNoteD) : zero ≤ x := by rw [← bot_eq_zero]; exact bot_le

theorem zero_lt_Omega (k : ℕ) : zero < Omega k := by
  rw [lt_iff_entries, entries_zero, entries_Omega]; exact ThetaWTerm.nil_lt_cons _ _

theorem omegaMul_le_omegaMul {a b : ThetaWNoteD} (h : a ≤ b) : omegaMul a ≤ omegaMul b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaMul_lt_omegaMul h)
  · exact le_refl _

theorem ofNat_le_ofNat {p q : ℕ} (h : p ≤ q) : ofNat p ≤ ofNat q := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (ofNat_lt_ofNat h)
  · exact le_refl _

theorem nadd_le_nadd_left' {a a' : ThetaWNoteD} (b : ThetaWNoteD) (h : a ≤ a') :
    nadd a b ≤ nadd a' b := by
  rw [nadd_comm a b, nadd_comm a' b]; exact nadd_le_nadd_right b h

theorem succ_le_succ {a b : ThetaWNoteD} (h : a ≤ b) : succ a ≤ succ b :=
  nadd_le_nadd_left' one h

theorem succ_lt_Omega_of_le {k : ℕ} {x : ThetaWNoteD} (h : succ x ≤ Omega k) : succ x < Omega k :=
  succ_lt_prin trivial (lt_of_lt_of_le (lt_succ x) h)

theorem lt_of_succ_lt {x p : ThetaWNoteD} (h : succ x < p) : x < p := lt_trans (lt_succ x) h

/-- `succ x ≺ p ↔ x ≺ p`, for principal `p`. -/
theorem succ_lt_prin_iff {x p : ThetaWNoteD} (hp : ThetaWTerm.IsPrin p.1) : succ x < p ↔ x < p :=
  ⟨lt_of_succ_lt, succ_lt_prin hp⟩

/-- **`Ω_k`, `k ∈ ℕ`, with `Ω_0 := 0`** (`ThetaWNoteD.Omega m` already denotes `Ω_{m+1}`). -/
def OmegaBelow : ℕ → ThetaWNoteD
  | 0 => zero
  | k + 1 => Omega k

@[simp] theorem OmegaBelow_zero : OmegaBelow 0 = zero := rfl

@[simp] theorem OmegaBelow_succ (k : ℕ) : OmegaBelow (k + 1) = Omega k := rfl

theorem Omega_lt_Omega_iff {i j : ℕ} : Omega i < Omega j ↔ i < j := by
  rw [lt_iff]; exact ThetaWTerm.Omega_lt_Omega_iff i j

theorem le_add_right (a b : ThetaWNoteD) : a ≤ a + b := by
  conv_lhs => rw [← add_zero a]
  exact add_le_add_left a (zero_le' b)

/-- **`Ω_k ≺ Ω_{k+1}`.** -/
theorem OmegaBelow_lt_Omega (k : ℕ) : OmegaBelow k < Omega k := by
  cases k with
  | zero => rw [OmegaBelow_zero, lt_iff_entries, entries_zero, entries_Omega]
            exact ThetaWTerm.nil_lt_cons _ _
  | succ m => rw [OmegaBelow_succ]; exact Omega_lt_Omega_iff.mpr (Nat.lt_succ_self m)

/-- **`Ω_j ⪯ Ω_k` for `j ≺ k`** (both read as the "`Ω_k`, `k ∈ ℕ`" indexing, `Omega_ = Ω_{·+1}`). -/
theorem Omega_le_OmegaBelow_of_lt {j k : ℕ} (h : j < k) : Omega j ≤ OmegaBelow k := by
  cases k with
  | zero => exact absurd h (Nat.not_lt_zero j)
  | succ m =>
    rw [OmegaBelow_succ]
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp h) with h' | rfl
    · exact le_of_lt (Omega_lt_Omega_iff.mpr h')
    · exact le_refl _

/-- `x + n = x ⊕ n`: the ordinary sum and the natural sum agree when the right summand is a
numeral (both `addL`/`mergeL` simply append `n` copies of the least term `0` at the end). -/
theorem add_ofNat_eq_nadd_ofNat (x : ThetaWNoteD) (p : ℕ) : x + ofNat p = nadd x (ofNat p) := by
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

/-- `(x ⊕ p) + 1 = x ⊕ (p + 1)`, for the successor of Definition 5.2. -/
theorem succ_add_ofNat (x : ThetaWNoteD) (p : ℕ) : succ (x + ofNat p) = x + ofNat (p + 1) := by
  rw [← add_one_eq_succ, add_assoc, add_one_eq_succ, ← ofNat_succ]

theorem entries_omegaMul_nadd_ofNat (a : ThetaWNoteD) (p : ℕ) :
    (nadd (omegaMul a) (ofNat p)).entries =
      a.entries.map ThetaWTerm.onePlus ++ List.replicate p (ThetaWTerm.sum []) := by
  have hs : ThetaWTerm.SortedDesc (a.entries.map ThetaWTerm.onePlus) := by
    have := sorted_entries (omegaMul a); rwa [entries_omegaMul] at this
  have hr : ThetaWTerm.SortedDesc (List.replicate p (ThetaWTerm.sum [])) :=
    List.pairwise_replicate.mpr (Or.inr (ThetaWTerm.le_refl' _))
  rw [entries_nadd, entries_omegaMul, entries_ofNat]
  refine ThetaWTerm.mergeL_eq_of_perm hs hr ?_ (List.Perm.refl _)
  refine List.pairwise_append.mpr ⟨hs, hr, fun x _ y hy => ?_⟩
  rw [List.eq_of_mem_replicate hy]
  exact ThetaWTerm.nil_le x

/-- **`ω · a ⊕ p ≺ ω · b` for `a ≺ b`**: a finite part never reaches the next multiple of `ω`
(ported from `Ordinal/Theta`, Freund Exercise 5.3, stage case). -/
theorem omegaMul_nadd_ofNat_lt {a b : ThetaWNoteD} (h : a < b) (p : ℕ) :
    nadd (omegaMul a) (ofNat p) < omegaMul b := by
  rw [lt_iff_entries, entries_omegaMul_nadd_ofNat, entries_omegaMul]
  exact ThetaWTerm.sum_map_onePlus_append_lt (fun _ hz => List.eq_of_mem_replicate hz)
    ((ThetaWTerm.sum_lt_sum_iff_lex _ _).mp (lt_iff_entries.mp h))
    (fun _ hx => (cnf_entries a).nf hx) (fun _ hy => (cnf_entries b).nf hy)

/-- **`(x + ω·a) ⊕ p ≺ x + ω·b` for `a ≺ b`**, `x` any fixed prefix — the `Ω_k +`-wrapped form of
`omegaMul_nadd_ofNat_lt` used for the stage rank drop at level `k` (`x := OmegaBelow k`). -/
theorem add_omegaMul_nadd_ofNat_lt (x : ThetaWNoteD) {a b : ThetaWNoteD} (h : a < b) (p : ℕ) :
    nadd (x + omegaMul a) (ofNat p) < x + omegaMul b := by
  rw [← add_ofNat_eq_nadd_ofNat, add_assoc, add_ofNat_eq_nadd_ofNat]
  exact add_lt_add_left x (omegaMul_nadd_ofNat_lt h p)

end ThetaWNoteD

namespace IDn

open LO LO.FirstOrder

/-! ### The rank -/

section Rank

variable {n : ℕ}

/-- The rank of an atom: `Ω_{s.lvl} + ω · s.val` for a stage `s`, `0` for `X` and arithmetic. -/
def atomRkStage (s : Stage n) : ThetaWNoteD := ThetaWNoteD.OmegaBelow s.lvl.val +
  ThetaWNoteD.omegaMul s.val

/-- The rank of a relation symbol. -/
def atomRk : {k : ℕ} → (LIinfN n).Rel k → ThetaWNoteD
  | _, Sum.inl _ => ThetaWNoteD.zero
  | _, Sum.inr IInfRelN.X => ThetaWNoteD.zero
  | _, Sum.inr (IInfRelN.stage s) => atomRkStage s

theorem atomRk_stage (s : Stage n) :
    atomRk (Sum.inr (IInfRelN.stage s) : (LIinfN n).Rel 1) = atomRkStage s := rfl

/-- The structural recursion behind `rk`. -/
def rkRec {ξ : Type*} : {m : ℕ} → Semiformula (LIinfN n) ξ m → ThetaWNoteD
  | _, .verum => ThetaWNoteD.zero
  | _, .falsum => ThetaWNoteD.zero
  | _, .rel r _ => atomRk r
  | _, .nrel r _ => atomRk r
  | _, .and φ ψ => ThetaWNoteD.succ (max (rkRec φ) (rkRec ψ))
  | _, .or φ ψ => ThetaWNoteD.succ (max (rkRec φ) (rkRec ψ))
  | _, .all φ => ThetaWNoteD.succ (rkRec φ)
  | _, .exs φ => ThetaWNoteD.succ (rkRec φ)

/-- **The rank** `rk(φ)` of Freund, Definition 5.2, read for `ID n` (design note §2.1). -/
irreducible_def rk {ξ : Type*} {m : ℕ} (φ : Semiformula (LIinfN n) ξ m) : ThetaWNoteD := rkRec φ

section Equations

variable {ξ : Type*} {m : ℕ}

@[simp] theorem rk_verum : rk (⊤ : Semiformula (LIinfN n) ξ m) = ThetaWNoteD.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_falsum : rk (⊥ : Semiformula (LIinfN n) ξ m) = ThetaWNoteD.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_rel {k : ℕ} (r : (LIinfN n).Rel k) (v : Fin k → Semiterm (LIinfN n) ξ m) :
    rk (Semiformula.rel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_nrel {k : ℕ} (r : (LIinfN n).Rel k) (v : Fin k → Semiterm (LIinfN n) ξ m) :
    rk (Semiformula.nrel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_and (φ ψ : Semiformula (LIinfN n) ξ m) :
    rk (φ ⋏ ψ) = ThetaWNoteD.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_or (φ ψ : Semiformula (LIinfN n) ξ m) :
    rk (φ ⋎ ψ) = ThetaWNoteD.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_all (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    rk (∀¹ φ) = ThetaWNoteD.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

@[simp] theorem rk_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    rk (∃¹ φ) = ThetaWNoteD.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

/-- `rk(I_k^{≺a} t) = Ω_k + ω · a`. -/
@[simp] theorem rk_stageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    rk (stageAt s t) = atomRkStage s := rk_rel _ _

/-- `rk(¬I_k^{≺a} t) = Ω_k + ω · a`. -/
@[simp] theorem rk_nstageAt (s : Stage n) (t : Semiterm (LIinfN n) ξ m) :
    rk (nstageAt s t) = atomRkStage s := rk_nrel _ _

/-- **`rk(I_k t) = Ω_{k+1}`**, since `ω · Ω_{k+1} = Ω_{k+1}` and `Ω_k + Ω_{k+1} = Ω_{k+1}`. -/
@[simp] theorem rk_IOmegaAt (k : Fin n) (t : Semiterm (LIinfN n) ξ m) :
    rk (IOmegaAt k t) = ThetaWNoteD.Omega k.val := by
  rw [IOmegaAt, rk_stageAt]
  show ThetaWNoteD.OmegaBelow (Stage.top k).lvl.val + ThetaWNoteD.omegaMul (Stage.top k).val = _
  rw [Stage.lvl_top, Stage.val_top, ThetaWNoteD.omegaMul_Omega _,
    ThetaWNoteD.add_Omega_of_lt (ThetaWNoteD.OmegaBelow_lt_Omega k.val)]

@[simp] theorem rk_XinfAt (t : Semiterm (LIinfN n) ξ m) : rk (XinfAt t) = ThetaWNoteD.zero :=
  rk_rel _ _

end Equations

/-! ### Negation and substitution -/

section Basic

variable {ξ : Type*} {m : ℕ}

/-- **`rk(¬φ) = rk(φ)`.** -/
@[simp] theorem rk_neg (φ : Semiformula (LIinfN n) ξ m) : rk (∼φ) = rk φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The rank does not see terms**: it is invariant under every rewriting. -/
@[simp] theorem rk_rew {ξ₁ ξ₂ : Type*} {m₁ m₂ : ℕ} (ω : Rew (LIinfN n) ξ₁ m₁ ξ₂ m₂)
    (φ : Semiformula (LIinfN n) ξ₁ m₁) : rk (ω ▹ φ) = rk φ := by
  induction φ using Semiformula.rec' generalizing m₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, rk_rel, rk_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, rk_nrel, rk_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem rk_subst (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ m) :
    rk (φ/[t]) = rk φ := rk_rew _ φ

theorem rk_subst_lt_all (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ 0) :
    rk (φ/[t]) < rk (∀¹ φ) := by
  rw [rk_subst, rk_all]; exact ThetaWNoteD.lt_succ _

theorem rk_subst_lt_exs (φ : Semiformula (LIinfN n) ξ 1) (t : Semiterm (LIinfN n) ξ 0) :
    rk (φ/[t]) < rk (∃¹ φ) := by
  rw [rk_subst, rk_exs]; exact ThetaWNoteD.lt_succ _

theorem rk_lt_all (φ : Semiformula (LIinfN n) ξ (m + 1)) : rk φ < rk (∀¹ φ) := by
  rw [rk_all]; exact ThetaWNoteD.lt_succ _

theorem rk_lt_exs (φ : Semiformula (LIinfN n) ξ (m + 1)) : rk φ < rk (∃¹ φ) := by
  rw [rk_exs]; exact ThetaWNoteD.lt_succ _

theorem rk_left_lt_and (φ ψ : Semiformula (LIinfN n) ξ m) : rk φ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaWNoteD.lt_succ _)

theorem rk_right_lt_and (φ ψ : Semiformula (LIinfN n) ξ m) : rk ψ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaWNoteD.lt_succ _)

theorem rk_left_lt_or (φ ψ : Semiformula (LIinfN n) ξ m) : rk φ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaWNoteD.lt_succ _)

theorem rk_right_lt_or (φ ψ : Semiformula (LIinfN n) ξ m) : rk ψ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaWNoteD.lt_succ _)

end Basic

/-! ### The finite-part bound and Exercise 5.3 -/

section Bound

variable {ξ : Type*} {m : ℕ}

theorem atomRk_le_of_forall {T : ThetaWNoteD} :
    ∀ {j : ℕ} (r : (LIinfN n).Rel j), (∀ s ∈ relParams r, atomRkStage s ≤ T) → atomRk r ≤ T
  | _, Sum.inl _, _ => ThetaWNoteD.zero_le' _
  | _, Sum.inr IInfRelN.X, _ => ThetaWNoteD.zero_le' _
  | _, Sum.inr (IInfRelN.stage s), h => h s rfl

/-- **The finite-part bound**: if every stage parameter of `φ` has `atomRkStage ≤ T`, then
`rk φ ≤ T ⊕ p` with `p` the logical complexity of `φ` — the per-level analogue of `ID1.Rank.
rk_le_omegaMul_nadd`, with `T` in place of `ω · μ` (there is no single quantity playing that role
once several levels are mixed; the caller supplies whatever bound its atoms satisfy). -/
theorem rk_le_add_ofNat {T : ThetaWNoteD} {φ : Semiformula (LIinfN n) ξ m}
    (h : ∀ s ∈ params φ, atomRkStage s ≤ T) :
    rk φ ≤ T + ThetaWNoteD.ofNat φ.complexity := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact ThetaWNoteD.zero_le' _
  | hfalsum => rw [rk_falsum]; exact ThetaWNoteD.zero_le' _
  | hrel r v => rw [rk_rel]; exact le_trans (atomRk_le_of_forall r h) (ThetaWNoteD.le_add_right _ _)
  | hnrel r v => rw [rk_nrel]; exact le_trans (atomRk_le_of_forall r h) (ThetaWNoteD.le_add_right _ _)
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, Semiformula.complexity_and, ← ThetaWNoteD.succ_add_ofNat]
    refine ThetaWNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans (ihφ fun s hs => h s (Or.inl hs))
        (ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans (ihψ fun s hs => h s (Or.inr hs))
        (ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, Semiformula.complexity_or, ← ThetaWNoteD.succ_add_ofNat]
    refine ThetaWNoteD.succ_le_succ (max_le ?_ ?_)
    · exact le_trans (ihφ fun s hs => h s (Or.inl hs))
        (ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans (ihψ fun s hs => h s (Or.inr hs))
        (ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.ofNat_le_ofNat (le_max_right _ _)))
  | hall φ ih =>
    rw [rk_all, Semiformula.complexity_all, ← ThetaWNoteD.succ_add_ofNat]
    exact ThetaWNoteD.succ_le_succ (ih h)
  | hexs φ ih =>
    rw [rk_exs, Semiformula.complexity_exs, ← ThetaWNoteD.succ_add_ofNat]
    exact ThetaWNoteD.succ_le_succ (ih h)

theorem atomRkStage_top (j : Fin n) : atomRkStage (Stage.top j) = ThetaWNoteD.Omega j.val := by
  show ThetaWNoteD.OmegaBelow (Stage.top j).lvl.val + ThetaWNoteD.omegaMul (Stage.top j).val = _
  rw [Stage.lvl_top, Stage.val_top, ThetaWNoteD.omegaMul_Omega _,
    ThetaWNoteD.add_Omega_of_lt (ThetaWNoteD.OmegaBelow_lt_Omega j.val)]

/-- **`rk(A_k(t, I_k^{≺a})) ⪯ (Ω_k + ω · a) ⊕ p`**, `p` the complexity, for `A` level-bounded
at `k`. -/
theorem rk_unfold_le {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    (a : StageAt k.val) (t : Semiterm (LIinfN n) ξ m) :
    rk (unfold A k a t) ≤
      (ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul a.1) +
        ThetaWNoteD.ofNat (unfold A k a t).complexity :=
  rk_le_add_ofNat fun s hs => by
    rcases params_unfold_of_levelBounded hb a t s hs with rfl | ⟨j, hj, rfl⟩
    · exact le_refl _
    · rw [atomRkStage_top]
      exact le_trans (ThetaWNoteD.Omega_le_OmegaBelow_of_lt hj) (ThetaWNoteD.le_add_right _ _)

/-- **Freund, Exercise 5.3, stage case, at level `k`**: `rk(A_k(t, I_k^{≺a})) ≺ rk(I_k^{≺a'} s)`
for `a ≺ a'` at the *same* level `k`. This is the rank drop of the infinite disjunction
`I_k^{≺a'} s ≃ ⋁_{a≺a'} A_k(s, I_k^{≺a})` and of the dual conjunction. -/
theorem rk_unfold_lt_stageAt {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    {a a' : StageAt k.val} (h : a.1 < a'.1) (t s : Semiterm (LIinfN n) ξ m) :
    rk (unfold A k a t) < rk (stageAt (⟨k, a'⟩ : Stage n) s) := by
  rw [rk_stageAt]
  show rk (unfold A k a t) < ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul a'.1
  have hbound := rk_unfold_le hb a t
  refine lt_of_le_of_lt hbound ?_
  rw [ThetaWNoteD.add_ofNat_eq_nadd_ofNat]
  exact ThetaWNoteD.add_omegaMul_nadd_ofNat_lt _ h _

theorem rk_unfold_lt_nstageAt {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    {a a' : StageAt k.val} (h : a.1 < a'.1) (t s : Semiterm (LIinfN n) ξ m) :
    rk (unfold A k a t) < rk (nstageAt (⟨k, a'⟩ : Stage n) s) := by
  rw [rk_nstageAt, ← rk_stageAt (⟨k, a'⟩ : Stage n) s]
  exact rk_unfold_lt_stageAt hb h t s

/-- A countable (`≺` top) stage of level `k` unfolds to a formula of rank `≺ Ω_{k+1}`. -/
theorem rk_unfold_lt_Omega {A : Semisentence (LXIn n) 1} {k : Fin n} (hb : LevelBounded k A)
    {a : StageAt k.val} (ha : a.1 < ThetaWNoteD.Omega k.val) (t : Semiterm (LIinfN n) ξ m) :
    rk (unfold A k a t) < ThetaWNoteD.Omega k.val := by
  have h := rk_unfold_lt_stageAt hb (a' := StageAt.top k.val) ha t t
  rw [show (⟨k, StageAt.top k.val⟩ : Stage n) = Stage.top k from rfl] at h
  rwa [← IOmegaAt_eq, rk_IOmegaAt] at h

end Bound

/-! ### Rank `Ω_{k+1}` and the class `Σ(Ω_{k+1})` -/

section Omega

variable {ξ : Type*} {m : ℕ}

/-- A stage index equals the top of its own level exactly when its value is that level's top
value — restates `stage_mk_eq_top_iff` (`IDn/Language.lean`) without first destructuring `s`. -/
theorem stage_eq_top_iff_of_lvl_eq {s : Stage n} {k : Fin n} (h : s.lvl = k) :
    s = Stage.top k ↔ s.val = ThetaWNoteD.Omega k.val := by
  obtain ⟨j, a⟩ := s
  have h' : j = k := h
  subst h'
  rw [stage_mk_eq_top_iff]
  exact Subtype.ext_iff

/-- **`Ω_j + ω · a ≺ Ω_{k+1}` iff `j ≤ k` and `(j, a) ≠ (k, Ω_{k+1})`** — the per-level analogue of
`ID1.atomRk_eq_Omega_of_mem`/the atom cases of `ID1.rk_lt_Omega_iff`: this is exactly `NrelSigmaW k`
read on the stage index. -/
theorem atomRkStage_lt_Omega_iff {k : Fin n} {s : Stage n} :
    atomRkStage s < ThetaWNoteD.Omega k.val ↔ s.lvl.val ≤ k.val ∧ s ≠ Stage.top k := by
  show ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val < ThetaWNoteD.Omega k.val ↔ _
  rcases lt_trichotomy s.lvl.val k.val with hlt | heq | hgt
  · have hval_le : ThetaWNoteD.omegaMul s.val ≤ ThetaWNoteD.Omega s.lvl.val := by
      rcases lt_or_eq_of_le s.le with h | h
      · exact le_of_lt (ThetaWNoteD.omegaMul_lt_prin trivial h)
      · rw [h, ThetaWNoteD.omegaMul_Omega _]
    have hsum_le : ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val ≤
        ThetaWNoteD.Omega s.lvl.val := by
      calc ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val
          ≤ ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.Omega s.lvl.val :=
            ThetaWNoteD.add_le_add_left _ hval_le
        _ = ThetaWNoteD.Omega s.lvl.val := ThetaWNoteD.add_Omega_of_lt
            (ThetaWNoteD.OmegaBelow_lt_Omega s.lvl.val)
    have hlhs : ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val <
        ThetaWNoteD.Omega k.val :=
      lt_of_le_of_lt hsum_le (ThetaWNoteD.Omega_lt_Omega_iff.mpr hlt)
    have hne : s ≠ Stage.top k :=
      Stage.ne_top_of_lvl_ne (fun e => absurd (congrArg Fin.val e) (Nat.ne_of_lt hlt))
    exact ⟨fun _ => ⟨le_of_lt hlt, hne⟩, fun _ => hlhs⟩
  · have homega_eq : ThetaWNoteD.Omega s.lvl.val = ThetaWNoteD.Omega k.val := by rw [heq]
    by_cases hval : s.val = ThetaWNoteD.Omega k.val
    · have hstop : s = Stage.top k := (stage_eq_top_iff_of_lvl_eq (Fin.ext heq)).mpr hval
      have heqrk : ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val =
          ThetaWNoteD.Omega k.val := by
        rw [hval, ThetaWNoteD.omegaMul_Omega _, heq, ThetaWNoteD.add_Omega_of_lt
          (ThetaWNoteD.OmegaBelow_lt_Omega k.val)]
      constructor
      · intro h; rw [heqrk] at h; exact absurd h (lt_irrefl _)
      · rintro ⟨-, hne'⟩; exact absurd hstop hne'
    · have hval' : s.val ≠ ThetaWNoteD.Omega s.lvl.val := by rw [homega_eq]; exact hval
      have hval_lt' : s.val < ThetaWNoteD.Omega s.lvl.val := lt_of_le_of_ne s.le hval'
      have h2 : ThetaWNoteD.OmegaBelow s.lvl.val + ThetaWNoteD.omegaMul s.val <
          ThetaWNoteD.Omega k.val := by
        rw [← homega_eq]
        exact ThetaWNoteD.add_lt_prin trivial (ThetaWNoteD.OmegaBelow_lt_Omega s.lvl.val)
          (ThetaWNoteD.omegaMul_lt_prin trivial hval_lt')
      have hne : s ≠ Stage.top k := by
        intro e
        exact hval ((stage_eq_top_iff_of_lvl_eq (Fin.ext heq)).mp e)
      exact ⟨fun _ => ⟨le_of_eq heq, hne⟩, fun _ => h2⟩
  · have hge : ThetaWNoteD.Omega k.val ≤ ThetaWNoteD.OmegaBelow s.lvl.val +
        ThetaWNoteD.omegaMul s.val :=
      le_trans (ThetaWNoteD.Omega_le_OmegaBelow_of_lt hgt) (ThetaWNoteD.le_add_right _ _)
    constructor
    · intro h; exact absurd h (not_lt_of_ge hge)
    · rintro ⟨h1, -⟩; exact absurd h1 (not_le_of_gt hgt)

/-- **A formula of rank `≺ Ω_{k+1}` has every stage parameter of level `≤ k` and `≠` the full
level-`k` predicate, and conversely** — the per-level analogue of `ID1.rk_lt_Omega_iff`. -/
theorem rk_lt_Omega_iff {k : Fin n} {φ : Semiformula (LIinfN n) ξ m} :
    rk φ < ThetaWNoteD.Omega k.val ↔ ∀ s ∈ params φ, s.lvl.val ≤ k.val ∧ s ≠ Stage.top k := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact ⟨fun _ s hs => (hs : False).elim,
      fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
  | hfalsum => rw [rk_falsum]; exact ⟨fun _ s hs => (hs : False).elim,
      fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
  | hrel r v =>
    rw [rk_rel]
    rcases r with r | r
    · exact ⟨fun _ s hs => (hs : False).elim, fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
    · cases r with
      | X => exact ⟨fun _ s hs => (hs : False).elim, fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
      | stage s =>
        show atomRkStage s < ThetaWNoteD.Omega k.val ↔ _
        rw [atomRkStage_lt_Omega_iff]
        exact ⟨fun h s' hs' => (show s' = s from hs') ▸ h, fun h => h s rfl⟩
  | hnrel r v =>
    rw [rk_nrel]
    rcases r with r | r
    · exact ⟨fun _ s hs => (hs : False).elim, fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
    · cases r with
      | X => exact ⟨fun _ s hs => (hs : False).elim, fun _ => ThetaWNoteD.zero_lt_Omega k.val⟩
      | stage s =>
        show atomRkStage s < ThetaWNoteD.Omega k.val ↔ _
        rw [atomRkStage_lt_Omega_iff]
        exact ⟨fun h s' hs' => (show s' = s from hs') ▸ h, fun h => h s rfl⟩
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, ThetaWNoteD.succ_lt_prin_iff (p := ThetaWNoteD.Omega k.val) trivial, max_lt_iff, ihφ, ihψ]
    constructor
    · rintro ⟨h1, h2⟩ s hs
      rcases hs with hs | hs
      · exact h1 s hs
      · exact h2 s hs
    · intro h
      exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, ThetaWNoteD.succ_lt_prin_iff (p := ThetaWNoteD.Omega k.val) trivial, max_lt_iff, ihφ, ihψ]
    constructor
    · rintro ⟨h1, h2⟩ s hs
      rcases hs with hs | hs
      · exact h1 s hs
      · exact h2 s hs
    · intro h
      exact ⟨fun s hs => h s (Or.inl hs), fun s hs => h s (Or.inr hs)⟩
  | hall φ ih => rw [rk_all, ThetaWNoteD.succ_lt_prin_iff (p := ThetaWNoteD.Omega k.val) trivial]; exact ih
  | hexs φ ih => rw [rk_exs, ThetaWNoteD.succ_lt_prin_iff (p := ThetaWNoteD.Omega k.val) trivial]; exact ih

/-- **A formula of rank `≺ Ω_{k+1}` is `Σ(Ω_{k+1})`, and so is its negation.** -/
theorem sigmaW_of_rk_lt_Omega {k : Fin n} {φ : Semiformula (LIinfN n) ξ m}
    (h : rk φ < ThetaWNoteD.Omega k.val) : SigmaW k φ ∧ SigmaW k (∼φ) :=
  sigmaW_and_neg_of_forall_params (rk_lt_Omega_iff.mp h)

end Omega

/-! ### Closure (Exercise 5.5(e)) and bounding -/

section Closure

variable {ξ : Type*} {m : ℕ}

/-- **Freund, Exercise 5.5(e), read for `ID n`**: the rank of `φ` lies in every set that contains
`0`, the atom-rank of every stage parameter of `φ`, and is closed under `+ 1`. Unlike `ID1.
rk_mem_of_closed`, there is no single "closed under `ω ·`" hypothesis to state once several levels
are mixed (the atom rank of a stage index is level-dependent), so the per-atom membership is
required directly as the hypothesis `h`. -/
theorem rk_mem_of_closed {S : Set ThetaWNoteD} (h0 : ThetaWNoteD.zero ∈ S)
    (hsucc : ∀ x ∈ S, ThetaWNoteD.succ x ∈ S) {φ : Semiformula (LIinfN n) ξ m}
    (h : ∀ s ∈ params φ, atomRkStage s ∈ S) : rk φ ∈ S := by
  have hmax : ∀ x y : ThetaWNoteD, x ∈ S → y ∈ S → max x y ∈ S := fun x y hx hy => by
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hxy]; exact hx
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact h0
  | hfalsum => rw [rk_falsum]; exact h0
  | hrel r v =>
    rw [rk_rel]
    rcases r with r | r
    · exact h0
    · cases r with
      | X => exact h0
      | stage s => exact h s rfl
  | hnrel r v =>
    rw [rk_nrel]
    rcases r with r | r
    · exact h0
    · cases r with
      | X => exact h0
      | stage s => exact h s rfl
  | hand φ ψ ihφ ihψ =>
    rw [rk_and]
    exact hsucc _ (hmax _ _ (ihφ fun s hs => h s (Or.inl hs)) (ihψ fun s hs => h s (Or.inr hs)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or]
    exact hsucc _ (hmax _ _ (ihφ fun s hs => h s (Or.inl hs)) (ihψ fun s hs => h s (Or.inr hs)))
  | hall φ ih => rw [rk_all]; exact hsucc _ (ih h)
  | hexs φ ih => rw [rk_exs]; exact hsucc _ (ih h)

/-- The bound of `rk_cap_le`'s atom case: bounding a stage index at level `k` never raises its
atom rank above `Ω_{k+1}` (needed since the capped value `⟨k, b⟩`'s own rank could otherwise be
compared against an unrelated `s`'s rank; in fact it is compared only against `atomRkStage
(Stage.top k) = Ω_{k+1}` below, but the bound holds unconditionally). -/
theorem atomRkStage_mk_le_Omega (k : Fin n) (b : StageAt k.val) :
    atomRkStage (⟨k, b⟩ : Stage n) ≤ ThetaWNoteD.Omega k.val := by
  show ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul b.1 ≤ _
  calc ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul b.1
      ≤ ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.omegaMul (ThetaWNoteD.Omega k.val) :=
        ThetaWNoteD.add_le_add_left _ (ThetaWNoteD.omegaMul_le_omegaMul b.2)
    _ = ThetaWNoteD.OmegaBelow k.val + ThetaWNoteD.Omega k.val := by
        rw [ThetaWNoteD.omegaMul_Omega _]
    _ = ThetaWNoteD.Omega k.val := ThetaWNoteD.add_Omega_of_lt (ThetaWNoteD.OmegaBelow_lt_Omega k.val)

theorem atomRk_capRelAt_le (k : Fin n) (b : StageAt k.val) :
    ∀ {j : ℕ} (r : (LIinfN n).Rel j), atomRk (capRelAt k b r) ≤ atomRk r
  | _, Sum.inl _ => le_refl _
  | _, Sum.inr IInfRelN.X => le_refl _
  | _, Sum.inr (IInfRelN.stage s) => by
    rw [capRelAt_stage]
    split_ifs with h
    · rw [atomRk_stage, atomRk_stage, h, atomRkStage_top]
      exact atomRkStage_mk_le_Omega k b
    · exact le_refl _

/-- **Bounding at level `k` does not raise the rank**: `rk(φ^β) ⪯ rk(φ)`. -/
theorem rk_capAt_le (k : Fin n) (b : StageAt k.val) (φ : Semiformula (LIinfN n) ξ m) :
    rk (capAt k b φ) ≤ rk φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact le_refl _
  | hfalsum => exact le_refl _
  | hrel r v => rw [capAt_rel, rk_rel, rk_rel]; exact atomRk_capRelAt_le k b r
  | hnrel r v => rw [capAt_nrel, rk_nrel, rk_nrel]; exact atomRk_capRelAt_le k b r
  | hand φ ψ ihφ ihψ =>
    rw [capAt_and, rk_and, rk_and]; exact ThetaWNoteD.succ_le_succ (max_le_max ihφ ihψ)
  | hor φ ψ ihφ ihψ =>
    rw [capAt_or, rk_or, rk_or]; exact ThetaWNoteD.succ_le_succ (max_le_max ihφ ihψ)
  | hall φ ih => rw [capAt_all, rk_all, rk_all]; exact ThetaWNoteD.succ_le_succ ih
  | hexs φ ih => rw [capAt_exs, rk_exs, rk_exs]; exact ThetaWNoteD.succ_le_succ ih

end Closure

/-! ### The generic successor -/

section Generic

variable {ξ : Type*} {m : ℕ}

theorem rk_and_succ (φ ψ : Semiformula (LIinfN n) ξ m) :
    rk (φ ⋏ ψ) = OrdinalNotation.succ (max (rk φ) (rk ψ)) := rk_and φ ψ

theorem rk_or_succ (φ ψ : Semiformula (LIinfN n) ξ m) :
    rk (φ ⋎ ψ) = OrdinalNotation.succ (max (rk φ) (rk ψ)) := rk_or φ ψ

theorem rk_all_succ (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    rk (∀¹ φ) = OrdinalNotation.succ (rk φ) := rk_all φ

theorem rk_exs_succ (φ : Semiformula (LIinfN n) ξ (m + 1)) :
    rk (∃¹ φ) = OrdinalNotation.succ (rk φ) := rk_exs φ

end Generic

end Rank

end IDn

end OrdinalAnalysis
