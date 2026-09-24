/-
  The rank of the formulas of the infinitary language of `ID₁`.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Definition 5.2, Exercise 5.3, Exercise 5.5(e), and
  the case distinctions on cut ranks in the proof of Theorem 6.7.

  **Definition 5.2.**

      rk(ψ)                         := 0          for a literal of arithmetic (and of `X`),
      rk(I^{≺α} t) := rk(¬I^{≺α} t) := ω · α,
      rk(ψ₀ ∨ ψ₁) := rk(ψ₀ ∧ ψ₁)    := max{rk ψ₀, rk ψ₁} + 1,
      rk(∃x ψ)    := rk(∀x ψ)       := rk ψ + 1.

  The values are ϑ-notations; `ω · α` is `ThetaNote.omegaMul` (Freund §5: `ω · Ω = Ω`,
  `ω · ϑα = ϑα`, `ω · ⟨α_i⟩ = ⟨1 + α_i⟩`), `+ 1` is `ThetaNote.succ` (`= α ⊕ 1 = α + 1`), and
  `max` is the maximum of the linear order.  None of them needs the well-foundedness of the
  notation.  The free predicate `X` is a literal of rank `0`, as arithmetic literals are.

  The rank is sealed (`irreducible_def`): it is computed through its equations, never by
  unfolding, since deciding `max` of notations by evaluation is expensive.

  **The laws.**

    * `rk (∼φ) = rk φ` (`rk_neg`), and the rank does not see terms (`rk_rew`, `rk_subst`),
      so an instance of a quantified formula has smaller rank (`rk_subst_lt_all`, …), and so
      has each conjunct and disjunct;
    * **Exercise 5.3, stage case**: `rk(A(t, I^{≺γ})) ≺ ω · α = rk(I^{≺α} s)` for `γ ≺ α`
      (`rk_unfold_lt_stageAt`), from `rk(A(t, I^{≺γ})) ⪯ ω · γ ⊕ n` and
      `ω · γ ⊕ n ≺ ω · α` (`ThetaNote.omegaMul_nadd_ofNat_lt`);
    * `rk(I^{≺α} t) ≺ Ω` for `α ≺ Ω`, and `rk(I t) = Ω`;
    * every rank is below `Ω + ω` (`rk_lt_Omega_nadd_omega`); a formula has rank `≺ Ω` iff
      `Ω ∉ k(φ)` (`rk_lt_Omega_iff`), and then it and its negation are `Σ(Ω)`;
    * a formula of rank `⪯ Ω` has rank `≺ Ω` or is `I t` or `¬I t`
      (`rk_le_Omega_cases`); for a `Σ(Ω)` formula only `I t` remains
      (`sigmaOmega_rk_le_Omega`).  These are the case distinctions on the cut formula in
      the proof of Theorem 6.7 (cut rank `Ω + 1`);
    * **Exercise 5.5(e)**: `rk φ` lies in every set containing `0` and `k(φ)` and closed
      under `ω ·` and `+ 1` (`rk_mem_of_closed`);
    * bounding does not raise the rank (`rk_cap_le`).

  With the well-foundedness of the ϑ-order, `ThetaNote` is an `OrdinalNotation`, and the
  successor of Definition 5.2 is the generic `OrdinalNotation.succ` (`rk_and_succ`, …), so
  the height and rank bookkeeping of the generic calculus applies verbatim.
-/
import OrdinalAnalysis.ID1.Language
import OrdinalAnalysis.Ordinal.Theta.WellFounded

set_option autoImplicit false

namespace OrdinalAnalysis

/-! ### `ω · α ⊕ n` below `ω · β`

Facts of the syntactic ϑ-arithmetic (Cantor exponent lists) needed for Exercise 5.3. -/

namespace ThetaTerm

theorem addL_zero_ne_nil : ∀ L : List ThetaTerm, addL [sum []] L ≠ []
  | [] => by simp [addL]
  | y :: ys => by rw [addL_cons]; simp

/-- `0 ≺ 1 + e`. -/
theorem nil_lt_onePlus (e : ThetaTerm) : sum [] < onePlus e := by
  apply nil_lt_of_ne
  intro h
  exact addL_zero_ne_nil (toList e) (ofList_injective (h.trans ofList_nil.symm))

/-- If `xs` is lexicographically below `ys`, then appending zero exponents to `xs` after
raising every exponent by `1 +` keeps it below `ys` raised the same way. -/
theorem sum_map_onePlus_append_lt {zs : List ThetaTerm} (hz : ∀ z ∈ zs, z = sum []) :
    ∀ {xs ys : List ThetaTerm}, List.Lex (· < ·) xs ys → (∀ x ∈ xs, NF x) →
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

end ThetaTerm

namespace ThetaNote

theorem zero_le' (x : ThetaNote) : zero ≤ x := bot_le

theorem zero_lt_Omega : zero < Omega := by
  rw [← ofNat_zero]; exact ofNat_lt_prin (p := Omega) trivial 0

theorem omegaMul_le_omegaMul {a b : ThetaNote} (h : a ≤ b) : omegaMul a ≤ omegaMul b := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (omegaMul_lt_omegaMul h)
  · exact le_refl _

theorem ofNat_le_ofNat {m n : ℕ} (h : m ≤ n) : ofNat m ≤ ofNat n := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (ofNat_lt_ofNat h)
  · exact le_refl _

theorem nadd_le_nadd_left' {a a' : ThetaNote} (b : ThetaNote) (h : a ≤ a') :
    ThetaNote.nadd a b ≤ ThetaNote.nadd a' b := by
  rw [nadd_comm a b, nadd_comm a' b]; exact nadd_le_nadd_right b h

theorem succ_le_succ {a b : ThetaNote} (h : a ≤ b) : succ a ≤ succ b :=
  nadd_le_nadd_left' one h

/-- `(β ⊕ n) + 1 = β ⊕ (n + 1)`. -/
theorem succ_nadd_ofNat (b : ThetaNote) (n : ℕ) :
    succ (ThetaNote.nadd b (ofNat n)) = ThetaNote.nadd b (ofNat (n + 1)) := by
  rw [ofNat_succ, succ, succ, nadd_assoc]

/-- The finite notations lie below `ω = ω^1`. -/
theorem ofNat_lt_omega (n : ℕ) : ofNat n < omegaPow one := by
  rw [lt_omegaPow_iff, entries_ofNat]
  intro e he
  rw [List.eq_of_mem_replicate he]
  exact zero_lt_one

/-- `x + 1 ≺ Ω` for `x ≺ Ω`, in the form used for ranks: a successor `⪯ Ω` is `≺ Ω`. -/
theorem succ_lt_Omega_of_le {x : ThetaNote} (h : succ x ≤ Omega) : succ x < Omega :=
  succ_lt_prin trivial (lt_of_lt_of_le (lt_succ x) h)

theorem entries_omegaMul_nadd_ofNat (a : ThetaNote) (n : ℕ) :
    (ThetaNote.nadd (omegaMul a) (ofNat n)).entries =
      a.entries.map ThetaTerm.onePlus ++ List.replicate n (ThetaTerm.sum []) := by
  have hs : ThetaTerm.SortedDesc (a.entries.map ThetaTerm.onePlus) := by
    have := sorted_entries (omegaMul a)
    rwa [entries_omegaMul] at this
  have hr : ThetaTerm.SortedDesc (List.replicate n (ThetaTerm.sum [])) :=
    List.pairwise_replicate.mpr (Or.inr (ThetaTerm.le_refl' _))
  rw [entries_nadd, entries_omegaMul, entries_ofNat]
  refine ThetaTerm.mergeL_eq_of_perm hs hr ?_ (List.Perm.refl _)
  refine List.pairwise_append.mpr ⟨hs, hr, fun x _ y hy => ?_⟩
  rw [List.eq_of_mem_replicate hy]
  exact ThetaTerm.nil_le x

/-- **`ω · α ⊕ n ≺ ω · β` for `α ≺ β`**: a finite part never reaches the next multiple of `ω`
(the arithmetic content of Freund, Exercise 5.3, stage case). -/
theorem omegaMul_nadd_ofNat_lt {a b : ThetaNote} (h : a < b) (n : ℕ) :
    ThetaNote.nadd (omegaMul a) (ofNat n) < omegaMul b := by
  rw [lt_iff_entries, entries_omegaMul_nadd_ofNat, entries_omegaMul]
  exact ThetaTerm.sum_map_onePlus_append_lt (fun _ hz => List.eq_of_mem_replicate hz)
    ((ThetaTerm.sum_lt_sum_iff_lex _ _).mp (lt_iff_entries.mp h))
    (fun _ hx => (cnf_entries a).nf hx) (fun _ hy => (cnf_entries b).nf hy)

end ThetaNote

namespace InductiveDef

open LO LO.FirstOrder

/-! ### The rank -/

/-- The rank of an atom: `ω · α` for `I^{≺α}`, `0` for `X` and arithmetic. -/
def atomRk : {k : ℕ} → LIinf.Rel k → ThetaNote
  | _, Sum.inl _ => ThetaNote.zero
  | _, Sum.inr IInfRel.X => ThetaNote.zero
  | _, Sum.inr (IInfRel.stage a) => ThetaNote.omegaMul a.1

/-- The structural recursion behind `rk`. -/
def rkRec {ξ : Type*} : {n : ℕ} → Semiformula LIinf ξ n → ThetaNote
  | _, .verum => ThetaNote.zero
  | _, .falsum => ThetaNote.zero
  | _, .rel r _ => atomRk r
  | _, .nrel r _ => atomRk r
  | _, .and φ ψ => ThetaNote.succ (max (rkRec φ) (rkRec ψ))
  | _, .or φ ψ => ThetaNote.succ (max (rkRec φ) (rkRec ψ))
  | _, .all φ => ThetaNote.succ (rkRec φ)
  | _, .exs φ => ThetaNote.succ (rkRec φ)

/-- **The rank** `rk(φ)` of Freund, Definition 5.2. -/
irreducible_def rk {ξ : Type*} {n : ℕ} (φ : Semiformula LIinf ξ n) : ThetaNote := rkRec φ

section Equations

variable {ξ : Type*} {n : ℕ}

@[simp] theorem rk_verum : rk (⊤ : Semiformula LIinf ξ n) = ThetaNote.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_falsum : rk (⊥ : Semiformula LIinf ξ n) = ThetaNote.zero := by
  rw [rk_def]; rfl

@[simp] theorem rk_rel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    rk (Semiformula.rel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_nrel {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n) :
    rk (Semiformula.nrel r v) = atomRk r := by
  rw [rk_def]; rfl

@[simp] theorem rk_and (φ ψ : Semiformula LIinf ξ n) :
    rk (φ ⋏ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_or (φ ψ : Semiformula LIinf ξ n) :
    rk (φ ⋎ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := by
  rw [rk_def, rk_def, rk_def]; rfl

@[simp] theorem rk_all (φ : Semiformula LIinf ξ (n + 1)) :
    rk (∀¹ φ) = ThetaNote.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

@[simp] theorem rk_exs (φ : Semiformula LIinf ξ (n + 1)) :
    rk (∃¹ φ) = ThetaNote.succ (rk φ) := by
  rw [rk_def, rk_def]; rfl

/-- `rk(I^{≺α} t) = ω · α`. -/
@[simp] theorem rk_stageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    rk (stageAt a t) = ThetaNote.omegaMul a.1 := rk_rel _ _

/-- `rk(¬I^{≺α} t) = ω · α`. -/
@[simp] theorem rk_nstageAt (a : Stage) (t : Semiterm LIinf ξ n) :
    rk (nstageAt a t) = ThetaNote.omegaMul a.1 := rk_nrel _ _

/-- **`rk(I t) = Ω`**, since `ω · Ω = Ω`. -/
@[simp] theorem rk_IOmegaAt (t : Semiterm LIinf ξ n) : rk (IOmegaAt t) = ThetaNote.Omega := by
  rw [IOmegaAt, rk_stageAt, Stage.top_val, ThetaNote.omegaMul_Omega]

@[simp] theorem rk_XinfAt (t : Semiterm LIinf ξ n) : rk (XinfAt t) = ThetaNote.zero :=
  rk_rel _ _

/-- **`rk(I^{≺α} t) ≺ Ω` for `α ≺ Ω`.** -/
theorem rk_stageAt_lt_Omega {a : Stage} (ha : a.1 < ThetaNote.Omega) (t : Semiterm LIinf ξ n) :
    rk (stageAt a t) < ThetaNote.Omega := by
  rw [rk_stageAt]; exact ThetaNote.omegaMul_lt_prin trivial ha

theorem rk_nstageAt_lt_Omega {a : Stage} (ha : a.1 < ThetaNote.Omega) (t : Semiterm LIinf ξ n) :
    rk (nstageAt a t) < ThetaNote.Omega := by
  rw [rk_nstageAt]; exact ThetaNote.omegaMul_lt_prin trivial ha

end Equations

/-! ### Negation and substitution -/

section Basic

variable {ξ : Type*} {n : ℕ}

/-- **`rk(¬φ) = rk(φ)`** (Freund, after Definition 5.2). -/
@[simp] theorem rk_neg (φ : Semiformula LIinf ξ n) : rk (∼φ) = rk φ := by
  induction φ using Semiformula.rec' <;> simp [*]

/-- **The rank does not see terms**: it is invariant under every rewriting. -/
@[simp] theorem rk_rew {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} (ω : Rew LIinf ξ₁ n₁ ξ₂ n₂)
    (φ : Semiformula LIinf ξ₁ n₁) : rk (ω ▹ φ) = rk φ := by
  induction φ using Semiformula.rec' generalizing n₂ with
  | hverum => simp
  | hfalsum => simp
  | hrel r v => rw [Semiformula.rew_rel, rk_rel, rk_rel]
  | hnrel r v => rw [Semiformula.rew_nrel, rk_nrel, rk_nrel]
  | hand φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hor φ ψ ihφ ihψ => simp [ihφ, ihψ]
  | hall φ ih => simp [ih]
  | hexs φ ih => simp [ih]

@[simp] theorem rk_subst (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ n) :
    rk (φ/[t]) = rk φ := rk_rew _ φ

/-- An instance of `∀x φ` has smaller rank than `∀x φ`. -/
theorem rk_subst_lt_all (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ 0) :
    rk (φ/[t]) < rk (∀¹ φ) := by
  rw [rk_subst, rk_all]; exact ThetaNote.lt_succ _

/-- An instance of `∃x φ` has smaller rank than `∃x φ`. -/
theorem rk_subst_lt_exs (φ : Semiformula LIinf ξ 1) (t : Semiterm LIinf ξ 0) :
    rk (φ/[t]) < rk (∃¹ φ) := by
  rw [rk_subst, rk_exs]; exact ThetaNote.lt_succ _

theorem rk_lt_all (φ : Semiformula LIinf ξ (n + 1)) : rk φ < rk (∀¹ φ) := by
  rw [rk_all]; exact ThetaNote.lt_succ _

theorem rk_lt_exs (φ : Semiformula LIinf ξ (n + 1)) : rk φ < rk (∃¹ φ) := by
  rw [rk_exs]; exact ThetaNote.lt_succ _

theorem rk_left_lt_and (φ ψ : Semiformula LIinf ξ n) : rk φ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaNote.lt_succ _)

theorem rk_right_lt_and (φ ψ : Semiformula LIinf ξ n) : rk ψ < rk (φ ⋏ ψ) := by
  rw [rk_and]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaNote.lt_succ _)

theorem rk_left_lt_or (φ ψ : Semiformula LIinf ξ n) : rk φ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_left _ _) (ThetaNote.lt_succ _)

theorem rk_right_lt_or (φ ψ : Semiformula LIinf ξ n) : rk ψ < rk (φ ⋎ ψ) := by
  rw [rk_or]; exact lt_of_le_of_lt (le_max_right _ _) (ThetaNote.lt_succ _)

end Basic

/-! ### The rank from the parameters -/

section Bound

variable {ξ : Type*} {n : ℕ}

theorem atomRk_le_omegaMul {m : ThetaNote} :
    ∀ {k : ℕ} (r : LIinf.Rel k), (∀ a ∈ relParams r, a ≤ m) → atomRk r ≤ ThetaNote.omegaMul m
  | _, Sum.inl _, _ => ThetaNote.zero_le' _
  | _, Sum.inr IInfRel.X, _ => ThetaNote.zero_le' _
  | _, Sum.inr (IInfRel.stage a), h => ThetaNote.omegaMul_le_omegaMul (h a.1 rfl)

/-- **The finite-part bound**: if every parameter of `φ` is `⪯ μ`, then
`rk φ ⪯ ω · μ ⊕ n` with `n` the logical complexity of `φ`. -/
theorem rk_le_omegaMul_nadd {m : ThetaNote} (φ : Semiformula LIinf ξ n)
    (h : ∀ a ∈ params φ, a ≤ m) :
    rk φ ≤ ThetaNote.nadd (ThetaNote.omegaMul m) (ThetaNote.ofNat φ.complexity) := by
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact ThetaNote.zero_le' _
  | hfalsum => rw [rk_falsum]; exact ThetaNote.zero_le' _
  | hrel r v =>
    rw [rk_rel]
    exact le_trans (atomRk_le_omegaMul r h) (ThetaNote.le_nadd_left _ _)
  | hnrel r v =>
    rw [rk_nrel]
    exact le_trans (atomRk_le_omegaMul r h) (ThetaNote.le_nadd_left _ _)
  | hand φ ψ ihφ ihψ =>
    rw [rk_and, Semiformula.complexity_and, ← ThetaNote.succ_nadd_ofNat]
    refine ThetaNote.succ_le_succ (max_le ?_ ?_)
    · exact le_trans (ihφ fun a ha => h a (Or.inl ha))
        (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans (ihψ fun a ha => h a (Or.inr ha))
        (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat (le_max_right _ _)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or, Semiformula.complexity_or, ← ThetaNote.succ_nadd_ofNat]
    refine ThetaNote.succ_le_succ (max_le ?_ ?_)
    · exact le_trans (ihφ fun a ha => h a (Or.inl ha))
        (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat (le_max_left _ _)))
    · exact le_trans (ihψ fun a ha => h a (Or.inr ha))
        (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat (le_max_right _ _)))
  | hall φ ih =>
    rw [rk_all, Semiformula.complexity_all, ← ThetaNote.succ_nadd_ofNat]
    exact ThetaNote.succ_le_succ (ih h)
  | hexs φ ih =>
    rw [rk_exs, Semiformula.complexity_exs, ← ThetaNote.succ_nadd_ofNat]
    exact ThetaNote.succ_le_succ (ih h)

theorem relParams_le_Omega :
    ∀ {k : ℕ} (r : LIinf.Rel k), ∀ a ∈ relParams r, a ≤ ThetaNote.Omega
  | _, Sum.inl _, _, h => False.elim h
  | _, Sum.inr IInfRel.X, _, h => False.elim h
  | _, Sum.inr (IInfRel.stage b), _, h => by rw [Set.mem_singleton_iff.mp h]; exact b.2

/-- Every parameter is a stage, hence `⪯ Ω`. -/
theorem params_le_Omega {φ : Semiformula LIinf ξ n} : ∀ a ∈ params φ, a ≤ ThetaNote.Omega := by
  induction φ using Semiformula.rec' with
  | hverum => exact fun _ h => False.elim h
  | hfalsum => exact fun _ h => False.elim h
  | hrel r v => exact relParams_le_Omega r
  | hnrel r v => exact relParams_le_Omega r
  | hand φ ψ ihφ ihψ => exact fun a h => h.elim (ihφ a) (ihψ a)
  | hor φ ψ ihφ ihψ => exact fun a h => h.elim (ihφ a) (ihψ a)
  | hall φ ih => exact ih
  | hexs φ ih => exact ih

/-- `rk φ ⪯ Ω ⊕ n`, `n` the complexity of `φ`. -/
theorem rk_le_Omega_nadd (φ : Semiformula LIinf ξ n) :
    rk φ ≤ ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat φ.complexity) := by
  have h := rk_le_omegaMul_nadd φ params_le_Omega
  rwa [ThetaNote.omegaMul_Omega] at h

/-- **Every rank is below `Ω + ω`.** -/
theorem rk_lt_Omega_nadd_omega (φ : Semiformula LIinf ξ n) :
    rk φ < ThetaNote.nadd ThetaNote.Omega (ThetaNote.omegaPow ThetaNote.one) :=
  lt_of_le_of_lt (rk_le_Omega_nadd φ)
    (ThetaNote.nadd_lt_nadd_right _ (ThetaNote.ofNat_lt_omega _))

/-- `rk(A(t, I^{≺α})) ⪯ ω · α ⊕ n`. -/
theorem rk_unfold_le (A : Semisentence LXI 1) (a : Stage) (t : Semiterm LIinf ξ n) :
    rk (unfold A a t) ≤
      ThetaNote.nadd (ThetaNote.omegaMul a.1) (ThetaNote.ofNat (unfold A a t).complexity) :=
  rk_le_omegaMul_nadd _ fun _ hx => le_of_eq (Set.mem_singleton_iff.mp (params_unfold A a t hx))

/-- **Freund, Exercise 5.3, stage case**: `rk(A(t, I^{≺γ})) ≺ rk(I^{≺α} s)` for `γ ≺ α`.
This is the rank drop of the infinite disjunction `I^{≺α} s ≃ ⋁_{γ≺α} A(s, I^{≺γ})` and of
the dual conjunction. -/
theorem rk_unfold_lt_stageAt (A : Semisentence LXI 1) {a b : Stage} (h : a.1 < b.1)
    (t : Semiterm LIinf ξ n) (s : Semiterm LIinf ξ n) :
    rk (unfold A a t) < rk (stageAt b s) := by
  rw [rk_stageAt]
  exact lt_of_le_of_lt (rk_unfold_le A a t) (ThetaNote.omegaMul_nadd_ofNat_lt h _)

theorem rk_unfold_lt_nstageAt (A : Semisentence LXI 1) {a b : Stage} (h : a.1 < b.1)
    (t : Semiterm LIinf ξ n) (s : Semiterm LIinf ξ n) :
    rk (unfold A a t) < rk (nstageAt b s) := by
  rw [rk_nstageAt, ← rk_stageAt b s]; exact rk_unfold_lt_stageAt A h t s

/-- A countable stage unfolds to a formula of countable rank. -/
theorem rk_unfold_lt_Omega (A : Semisentence LXI 1) {a : Stage} (ha : a.1 < ThetaNote.Omega)
    (t : Semiterm LIinf ξ n) : rk (unfold A a t) < ThetaNote.Omega := by
  have h := rk_unfold_lt_stageAt A (b := Stage.top) ha t t
  rwa [← IOmegaAt_eq, rk_IOmegaAt] at h

end Bound

/-! ### Rank `Ω` and the class `Σ(Ω)` -/

section Omega

variable {ξ : Type*} {n : ℕ}

theorem atomRk_eq_Omega_of_mem :
    ∀ {k : ℕ} (r : LIinf.Rel k), ThetaNote.Omega ∈ relParams r → atomRk r = ThetaNote.Omega
  | _, Sum.inl _, h => False.elim h
  | _, Sum.inr IInfRel.X, h => False.elim h
  | _, Sum.inr (IInfRel.stage a), h => by
    show ThetaNote.omegaMul a.1 = _
    rw [← Set.mem_singleton_iff.mp h, ThetaNote.omegaMul_Omega]

/-- A formula with the parameter `Ω` has rank `⪰ Ω`. -/
theorem Omega_le_rk_of_mem {φ : Semiformula LIinf ξ n} (h : ThetaNote.Omega ∈ params φ) :
    ThetaNote.Omega ≤ rk φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact False.elim h
  | hfalsum => exact False.elim h
  | hrel r v => rw [rk_rel, atomRk_eq_Omega_of_mem r h]
  | hnrel r v => rw [rk_nrel, atomRk_eq_Omega_of_mem r h]
  | hand φ ψ ihφ ihψ =>
    rcases h with h | h
    · exact le_trans (ihφ h) (le_of_lt (rk_left_lt_and φ ψ))
    · exact le_trans (ihψ h) (le_of_lt (rk_right_lt_and φ ψ))
  | hor φ ψ ihφ ihψ =>
    rcases h with h | h
    · exact le_trans (ihφ h) (le_of_lt (rk_left_lt_or φ ψ))
    · exact le_trans (ihψ h) (le_of_lt (rk_right_lt_or φ ψ))
  | hall φ ih => exact le_trans (ih h) (le_of_lt (rk_lt_all φ))
  | hexs φ ih => exact le_trans (ih h) (le_of_lt (rk_lt_exs φ))

/-- **A formula of rank `≺ Ω` does not mention `I = I^{≺Ω}`, and conversely.** -/
theorem rk_lt_Omega_iff {φ : Semiformula LIinf ξ n} :
    rk φ < ThetaNote.Omega ↔ ThetaNote.Omega ∉ params φ := by
  constructor
  · intro h hm
    exact absurd (Omega_le_rk_of_mem hm) (not_le_of_gt h)
  · intro hm
    have hle : ∀ a ∈ params φ, a < ThetaNote.Omega := fun a ha =>
      lt_of_le_of_ne (params_le_Omega a ha) (fun e => hm (e ▸ ha))
    clear hm
    induction φ using Semiformula.rec' with
    | hverum => rw [rk_verum]; exact ThetaNote.zero_lt_Omega
    | hfalsum => rw [rk_falsum]; exact ThetaNote.zero_lt_Omega
    | hrel r v =>
      rw [rk_rel]
      rcases r with r | r
      · exact ThetaNote.zero_lt_Omega
      · cases r with
        | X => exact ThetaNote.zero_lt_Omega
        | stage a => exact ThetaNote.omegaMul_lt_prin trivial (hle a.1 rfl)
    | hnrel r v =>
      rw [rk_nrel]
      rcases r with r | r
      · exact ThetaNote.zero_lt_Omega
      · cases r with
        | X => exact ThetaNote.zero_lt_Omega
        | stage a => exact ThetaNote.omegaMul_lt_prin trivial (hle a.1 rfl)
    | hand φ ψ ihφ ihψ =>
      rw [rk_and]
      exact ThetaNote.succ_lt_prin trivial
        (max_lt (ihφ fun a ha => hle a (Or.inl ha)) (ihψ fun a ha => hle a (Or.inr ha)))
    | hor φ ψ ihφ ihψ =>
      rw [rk_or]
      exact ThetaNote.succ_lt_prin trivial
        (max_lt (ihφ fun a ha => hle a (Or.inl ha)) (ihψ fun a ha => hle a (Or.inr ha)))
    | hall φ ih => rw [rk_all]; exact ThetaNote.succ_lt_prin trivial (ih hle)
    | hexs φ ih => rw [rk_exs]; exact ThetaNote.succ_lt_prin trivial (ih hle)

/-- **A formula of rank `≺ Ω` is `Σ(Ω)`, and so is its negation** (Freund, proof of
Theorem 6.7: "`ψ` and `¬ψ` are `Σ(Ω)`-formulas"). -/
theorem sigmaOmega_of_rk_lt_Omega {φ : Semiformula LIinf ξ n} (h : rk φ < ThetaNote.Omega) :
    SigmaOmega φ ∧ SigmaOmega (∼φ) :=
  sigmaOmega_and_neg_of_Omega_not_mem (rk_lt_Omega_iff.mp h)

theorem rel_cases_le_Omega :
    ∀ {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n),
      atomRk r < ThetaNote.Omega ∨ ∃ t, Semiformula.rel r v = IOmegaAt t
  | _, Sum.inl _, _ => Or.inl ThetaNote.zero_lt_Omega
  | _, Sum.inr IInfRel.X, _ => Or.inl ThetaNote.zero_lt_Omega
  | _, Sum.inr (IInfRel.stage a), v => by
    by_cases ha : a = Stage.top
    · subst ha; exact Or.inr ⟨v 0, rel_eq_vec _ v⟩
    · exact Or.inl (ThetaNote.omegaMul_lt_prin trivial (Stage.lt_Omega_of_ne_top ha))

theorem nrel_cases_le_Omega :
    ∀ {k : ℕ} (r : LIinf.Rel k) (v : Fin k → Semiterm LIinf ξ n),
      atomRk r < ThetaNote.Omega ∨ ∃ t, Semiformula.nrel r v = ∼(IOmegaAt t)
  | _, Sum.inl _, _ => Or.inl ThetaNote.zero_lt_Omega
  | _, Sum.inr IInfRel.X, _ => Or.inl ThetaNote.zero_lt_Omega
  | _, Sum.inr (IInfRel.stage a), v => by
    by_cases ha : a = Stage.top
    · subst ha; exact Or.inr ⟨v 0, nrel_eq_vec _ v⟩
    · exact Or.inl (ThetaNote.omegaMul_lt_prin trivial (Stage.lt_Omega_of_ne_top ha))

/-- **A formula of rank `⪯ Ω` has rank `≺ Ω`, or it is `I t` or `¬I t`** (Freund, proof of
Theorem 6.7: a cut formula of rank `Ω` "must be of the form `It` or `¬It`"). -/
theorem rk_le_Omega_cases {φ : Semiformula LIinf ξ n} (h : rk φ ≤ ThetaNote.Omega) :
    rk φ < ThetaNote.Omega ∨ (∃ t, φ = IOmegaAt t) ∨ (∃ t, φ = ∼(IOmegaAt t)) := by
  cases φ with
  | verum => exact Or.inl (by rw [show rk (Semiformula.verum : Semiformula LIinf ξ n)
      = ThetaNote.zero from rk_verum]; exact ThetaNote.zero_lt_Omega)
  | falsum => exact Or.inl (by rw [show rk (Semiformula.falsum : Semiformula LIinf ξ n)
      = ThetaNote.zero from rk_falsum]; exact ThetaNote.zero_lt_Omega)
  | rel r v =>
    rcases rel_cases_le_Omega r v with h' | h'
    · exact Or.inl (by rw [rk_rel]; exact h')
    · exact Or.inr (Or.inl h')
  | nrel r v =>
    rcases nrel_cases_le_Omega r v with h' | h'
    · exact Or.inl (by rw [rk_nrel]; exact h')
    · exact Or.inr (Or.inr h')
  | and φ ψ =>
    have e : rk (Semiformula.and φ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := rk_and φ ψ
    rw [e] at h ⊢
    exact Or.inl (ThetaNote.succ_lt_Omega_of_le h)
  | or φ ψ =>
    have e : rk (Semiformula.or φ ψ) = ThetaNote.succ (max (rk φ) (rk ψ)) := rk_or φ ψ
    rw [e] at h ⊢
    exact Or.inl (ThetaNote.succ_lt_Omega_of_le h)
  | all φ =>
    have e : rk (Semiformula.all φ) = ThetaNote.succ (rk φ) := rk_all φ
    rw [e] at h ⊢
    exact Or.inl (ThetaNote.succ_lt_Omega_of_le h)
  | exs φ =>
    have e : rk (Semiformula.exs φ) = ThetaNote.succ (rk φ) := rk_exs φ
    rw [e] at h ⊢
    exact Or.inl (ThetaNote.succ_lt_Omega_of_le h)

/-- **A `Σ(Ω)` formula of rank `⪯ Ω` has rank `≺ Ω` or is `I t`.** -/
theorem sigmaOmega_rk_le_Omega {φ : Semiformula LIinf ξ n} (hφ : SigmaOmega φ)
    (h : rk φ ≤ ThetaNote.Omega) : rk φ < ThetaNote.Omega ∨ ∃ t, φ = IOmegaAt t := by
  rcases rk_le_Omega_cases h with h' | h' | ⟨t, rfl⟩
  · exact Or.inl h'
  · exact Or.inr h'
  · exact absurd hφ (not_sigmaOmega_neg_IOmegaAt t)

end Omega

/-! ### Closure (Exercise 5.5(e)) and bounding -/

section Closure

variable {ξ : Type*} {n : ℕ}

/-- **Freund, Exercise 5.5(e)**: the rank of `φ` lies in every set that contains `0` and
the parameters of `φ` and is closed under `ω ·` and `+ 1`.  For a nice operator `H` this is
`rk φ ∈ H(k(φ))`. -/
theorem rk_mem_of_closed {S : Set ThetaNote} (h0 : ThetaNote.zero ∈ S)
    (hmul : ∀ x ∈ S, ThetaNote.omegaMul x ∈ S) (hsucc : ∀ x ∈ S, ThetaNote.succ x ∈ S)
    {φ : Semiformula LIinf ξ n} (h : params φ ⊆ S) : rk φ ∈ S := by
  have hmax : ∀ x y : ThetaNote, x ∈ S → y ∈ S → max x y ∈ S := fun x y hx hy => by
    rcases le_total x y with hxy | hxy
    · rw [max_eq_right hxy]; exact hy
    · rw [max_eq_left hxy]; exact hx
  have hatom : ∀ {k : ℕ} (r : LIinf.Rel k), relParams r ⊆ S → atomRk r ∈ S := by
    intro k r hr
    rcases r with r | r
    · exact h0
    · cases r with
      | X => exact h0
      | stage a => exact hmul a.1 (hr rfl)
  induction φ using Semiformula.rec' with
  | hverum => rw [rk_verum]; exact h0
  | hfalsum => rw [rk_falsum]; exact h0
  | hrel r v => rw [rk_rel]; exact hatom r h
  | hnrel r v => rw [rk_nrel]; exact hatom r h
  | hand φ ψ ihφ ihψ =>
    rw [rk_and]
    exact hsucc _ (hmax _ _ (ihφ fun _ ha => h (Or.inl ha)) (ihψ fun _ ha => h (Or.inr ha)))
  | hor φ ψ ihφ ihψ =>
    rw [rk_or]
    exact hsucc _ (hmax _ _ (ihφ fun _ ha => h (Or.inl ha)) (ihψ fun _ ha => h (Or.inr ha)))
  | hall φ ih => rw [rk_all]; exact hsucc _ (ih h)
  | hexs φ ih => rw [rk_exs]; exact hsucc _ (ih h)

theorem atomRk_capRel_le (b : Stage) :
    ∀ {k : ℕ} (r : LIinf.Rel k), atomRk (capRel b r) ≤ atomRk r
  | _, Sum.inl _ => le_refl _
  | _, Sum.inr IInfRel.X => le_refl _
  | _, Sum.inr (IInfRel.stage a) => by
    show ThetaNote.omegaMul (if a = Stage.top then b else a).1 ≤ ThetaNote.omegaMul a.1
    by_cases h : a = Stage.top
    · rw [if_pos h, h]; exact ThetaNote.omegaMul_le_omegaMul b.2
    · rw [if_neg h]

/-- **Bounding does not raise the rank**: `rk(φ^β) ⪯ rk(φ)`. -/
theorem rk_cap_le (b : Stage) (φ : Semiformula LIinf ξ n) : rk (cap b φ) ≤ rk φ := by
  induction φ using Semiformula.rec' with
  | hverum => exact le_refl _
  | hfalsum => exact le_refl _
  | hrel r v => rw [cap_rel, rk_rel, rk_rel]; exact atomRk_capRel_le b r
  | hnrel r v => rw [cap_nrel, rk_nrel, rk_nrel]; exact atomRk_capRel_le b r
  | hand φ ψ ihφ ihψ =>
    rw [cap_and, rk_and, rk_and]; exact ThetaNote.succ_le_succ (max_le_max ihφ ihψ)
  | hor φ ψ ihφ ihψ =>
    rw [cap_or, rk_or, rk_or]; exact ThetaNote.succ_le_succ (max_le_max ihφ ihψ)
  | hall φ ih => rw [cap_all, rk_all, rk_all]; exact ThetaNote.succ_le_succ ih
  | hexs φ ih => rw [cap_exs, rk_exs, rk_exs]; exact ThetaNote.succ_le_succ ih

end Closure

/-! ### The generic successor -/

section Generic

variable {ξ : Type*} {n : ℕ}

theorem rk_and_succ (φ ψ : Semiformula LIinf ξ n) :
    rk (φ ⋏ ψ) = OrdinalNotation.succ (max (rk φ) (rk ψ)) := rk_and φ ψ

theorem rk_or_succ (φ ψ : Semiformula LIinf ξ n) :
    rk (φ ⋎ ψ) = OrdinalNotation.succ (max (rk φ) (rk ψ)) := rk_or φ ψ

theorem rk_all_succ (φ : Semiformula LIinf ξ (n + 1)) :
    rk (∀¹ φ) = OrdinalNotation.succ (rk φ) := rk_all φ

theorem rk_exs_succ (φ : Semiformula LIinf ξ (n + 1)) :
    rk (∃¹ φ) = OrdinalNotation.succ (rk φ) := rk_exs φ

end Generic

end InductiveDef

end OrdinalAnalysis
