/-
  The embedding of `ID₁` into the operator-controlled infinitary calculus.

  Source: A. Freund, *Impredicativity and trees with gap condition: a second course on
  ordinal analysis*, arXiv:2204.09321, Theorem 6.5 ("Embedding"): given `ID₁ ⊢ ψ`, we
  obtain `H ⊢^{Ω·2+n}_{Ω+m} ψ⁺` for any nice operator `H` and some `m, n ∈ ℕ`.

  **The proof, as in the source.**  A proof of `σ` from finitely many axioms `θ_i` of `ID₁`
  is a finitary derivation of `σ, ¬θ_0, …, ¬θ_{k−1}` (Foundation's `⊢ᴸᴷ¹`, with cuts).  By
  induction over it (`replay`) the calculus derives every numeral instance of the embedded
  sequent at height `Ω + h` and cut rank `Ω + m`: the identity axioms by Lemma 6.1 (the
  atoms have rank at most `Ω`), the propositional rules by clauses (V) and (W), `∀` by the
  ω-rule (the eigenvariable ranges over the numerals), `∃` by clause (W) at the numeral of
  the value of the witness — the replacement of a closed term by its numeral
  (`IDerivable.replace_head`, Freund's remark in the proof of Proposition 6.4) — and a cut
  by a cut of rank `rk ψ⁺ ≺ Ω + m`.  Every rank has the form `ω · α + j` with `α ⪯ Ω`, so
  finitely many cuts against the axioms, each derivable at height `Ω · 2 + n(i)`
  (`AxDerivable`: Lemma 6.1 and ω-completeness for the axioms of `PA⁻` and of equality,
  the chain for induction, Proposition 6.2 for the closure axiom, Proposition 6.4 for the
  induction axiom of `I`), remove the axioms (`cut_axioms`).

  **Deviations from the source.**

    * *Cuts in the finitary derivation.*  Freund starts from a cut-free `PL`-derivation;
      the replay here accepts cuts, and the cut rank of the result is read off the
      derivation (`cutCx`).  The bound has Freund's form `Ω + m` either way.
    * *The free predicate `X`.*  The language `LXI` of `ID1 A` has the predicate `X`, which
      Freund's `L_ID` does not, and the identity clause `idX` of the calculus compares
      the arguments of `X`-literals syntactically.  The embedding reads `X` as the empty
      predicate (`embK = embed ∘ killX`), which is the reading of `X` in `stdInf`; for an
      `X`-free sentence `embK σ = embed σ = σ⁺` (`embedding_theorem_xfree`).  This is not
      a weakening of the bounds but of the statement for sentences mentioning `X`: in
      the calculus as built, `embed σ` itself is not derivable in general.  For the
      positive, `X`-free form `A := ⊥`, the induction axiom
      `X(0) ∧ ∀x (X x → X(x+1)) → ∀x X x` of `ID1 A` is false under the reading of `X` as the
      set `{0, 0+1}` of closed terms (every clause of the calculus, including `idX`, is
      sound for readings of `X` by sets of closed terms, the stages being empty); its
      embedding therefore has no derivation.
    * *The operator form.*  The operator form is required to be `X`-free (`XFreeL A`):
      the unfolding `A(t, I^{≺γ})` of a stage atom carries the term `t` into the
      arguments of `A`, and term replacement inside `X`-literals is not available.  The
      intended form `accForm` is `X`-free.
    * *Heights.*  The replay is at height `Ω + h` with `h` finite (Freund: `Ω + ω · l`);
      all heights are uniform in the nice operator, so `m` and `n` are chosen before `H`.

  Contents.

    `hgt`, `cutCx`                     height and cut complexity of an `LK` derivation
    `tr_*`                             the translation under an assignment
    `replay`                           **the replay**
    `ax_derivable_of_mem`              every axiom of `ID1 A`
    `cut_axioms`                       cutting away the axioms
    `embedding_theorem`                **Theorem 6.5**
    `embedding_theorem_xfree`          the form `H ⊢^{Ω·2+n}_{Ω+m} σ⁺` for `X`-free `σ`
-/
import OrdinalAnalysis.ID1.AxiomsID

set_option autoImplicit false

namespace OrdinalAnalysis

namespace InductiveDef

open LO LO.FirstOrder
open LO.FirstOrder.Rewriting LO.FirstOrder.TransitiveRewriting
open LO.FirstOrder.LawfulSyntacticRewriting
open LO.FirstOrder.Arithmetic

/-! ### Height and cut complexity of a finitary derivation -/

/-- The height of the replay of an `LK` derivation, above `Ω`. -/
def hgt : {Γ : Sequent LXI} → ⊢ᴸᴷ¹ Γ → ℕ
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, Derivation.cut dp dn => max (hgt dp) (hgt dn) + 1
  | _, Derivation.contraction d _ => hgt d
  | _, Derivation.or d => hgt d + 2
  | _, Derivation.and dp dq => max (hgt dp) (hgt dq) + 1
  | _, Derivation.all d => hgt d + 1
  | _, Derivation.exs d => hgt d + 1

/-- One more than the largest complexity of an embedded cut formula. -/
def cutCx : {Γ : Sequent LXI} → ⊢ᴸᴷ¹ Γ → ℕ
  | _, Derivation.identity _ _ => 0
  | _, Derivation.verum => 0
  | _, @Derivation.cut _ φ _ _ dp dn => max ((embK φ).complexity + 1) (max (cutCx dp) (cutCx dn))
  | _, Derivation.contraction d _ => cutCx d
  | _, Derivation.or d => cutCx d
  | _, Derivation.and dp dq => max (cutCx dp) (cutCx dq)
  | _, Derivation.all d => cutCx d
  | _, Derivation.exs d => cutCx d

/-! ### The translation under an assignment -/

section Tr

theorem tr_or (f : ℕ → ℕ) (φ ψ : Proposition LXI) : tr f (φ ⋎ ψ) = tr f φ ⋎ tr f ψ := by
  simp [tr]

theorem tr_and (f : ℕ → ℕ) (φ ψ : Proposition LXI) : tr f (φ ⋏ ψ) = tr f φ ⋏ tr f ψ := by
  simp [tr]

theorem tr_verum (f : ℕ → ℕ) : tr f ⊤ = ⊤ := by simp [tr]

theorem tr_all (f : ℕ → ℕ) (φ : Semiproposition LXI 1) :
    tr f (∀¹ φ) = ∀¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_all, numSubst_all]

theorem tr_exs (f : ℕ → ℕ) (φ : Semiproposition LXI 1) :
    tr f (∃¹ φ) = ∃¹ (numSubst₁ f ▹ embK φ) := by
  rw [tr, embK_exs, numSubst_exs]

theorem tr_free (f : ℕ → ℕ) (n : ℕ) (φ : Semiproposition LXI 1) :
    tr (n :>ₙ f) (Rewriting.free φ) = (numSubst₁ f ▹ embK φ)/[numI n] := by
  rw [tr, embK_free, numSubst_free]

theorem tr_shifts (f : ℕ → ℕ) (n : ℕ) (Γ : Sequent LXI) :
    (Γ⁺).map (tr (n :>ₙ f)) = Γ.map (tr f) := by
  induction Γ with
  | nil => rfl
  | cons φ Γ ih =>
    rw [Rewriting.shifts_cons, List.map_cons, List.map_cons, ih, tr, tr, embK_shift,
      numSubst_shift]

theorem tr_subst (f : ℕ → ℕ) (φ : Semiproposition LXI 1) (t : SyntacticTerm LXI) :
    tr f (φ/[t]) = (numSubst₁ f ▹ embK φ)/[numSubst f (embT t)] := by
  rw [tr, embK_subst₁, numSubst_subst]

theorem params_tr_sub {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    (f : ℕ → ℕ) (φ : Proposition LXI) : params (tr f φ) ⊆ H ∅ :=
  (params_tr f φ).trans (Set.singleton_subset_iff.mpr hH.Omega_mem)

theorem paramsList_map_tr {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H)
    (f : ℕ → ℕ) (Γ : Sequent LXI) : paramsList (Γ.map (tr f)) ⊆ H ∅ := by
  intro x ⟨χ, hχ, hx⟩
  obtain ⟨φ, -, rfl⟩ := List.mem_map.mp hχ
  exact params_tr_sub hH f φ hx

theorem paramsList_cons_sub {H : Set ThetaNote → Set ThetaNote} {φ : Proposition LIinf}
    {Γ : Sequent LIinf} (h1 : params φ ⊆ H ∅) (h2 : paramsList Γ ⊆ H ∅) :
    paramsList (φ :: Γ) ⊆ H ∅ := by
  rw [paramsList_cons]; exact Set.union_subset h1 h2

/-- The embedded formula of an atom has rank at most `Ω`: its complexity is `0`. -/
theorem omegaMul_rk_tr_atom_le (f : ℕ → ℕ) {k : ℕ} (r : LXI.Rel k)
    (v : Fin k → SyntacticTerm LXI) :
    ThetaNote.omegaMul (rk (tr f (Semiformula.rel r v))) ≤ ThetaNote.Omega := by
  have hc : (tr f (Semiformula.rel r v)).complexity = 0 := by
    rw [tr, Semiformula.complexity_rew]
    rcases r with r | r
    · rfl
    · cases r <;> rfl
  have h := omegaMul_rk_le (tr f (Semiformula.rel r v))
  rwa [hc, ThetaNote.ofNat_zero, ThetaNote.omegaMul_zero, ThetaNote.nadd_zero] at h

theorem rk_tr_lt (f : ℕ → ℕ) (φ : Proposition LXI) {m : ℕ}
    (hm : (embK φ).complexity + 1 ≤ m) :
    rk (tr f φ) < ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat m) := by
  refine lt_of_le_of_lt (rk_le_Omega_nadd _) (ThetaNote.nadd_lt_nadd_right _
    (ThetaNote.ofNat_lt_ofNat ?_))
  rw [tr, Semiformula.complexity_rew]; omega

end Tr

/-! ### The replay -/

section Replay

variable {A : Semisentence LXI 1} {H : Set ThetaNote → Set ThetaNote}

/-- `Ω ⊕ j`. -/
abbrev OmegaPlus (j : ℕ) : ThetaNote := ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat j)

theorem OmegaPlus_mem (hH : ThetaNote.Nice H) (j : ℕ) : OmegaPlus j ∈ H ∅ :=
  hH.nadd_mem hH.Omega_mem (hH.ofNat_mem j)

theorem OmegaPlus_lt {j k : ℕ} (h : j < k) : OmegaPlus j < OmegaPlus k :=
  ThetaNote.nadd_ofNat_lt_nadd_ofNat _ h

theorem OmegaPlus_le {j k : ℕ} (h : j ≤ k) : OmegaPlus j ≤ OmegaPlus k :=
  ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat h)

theorem one_lt_OmegaPlus (j : ℕ) : ThetaNote.one < OmegaPlus j :=
  lt_of_lt_of_le (ThetaNote.one_lt_prin (p := ThetaNote.Omega) trivial) (ThetaNote.le_nadd_left _ _)

theorem ofNat_lt_OmegaPlus (n j : ℕ) : ThetaNote.ofNat n < OmegaPlus j :=
  lt_of_lt_of_le (ThetaNote.ofNat_lt_prin (p := ThetaNote.Omega) trivial n)
    (ThetaNote.le_nadd_left _ _)

theorem subset_cons_cons {α : Type*} {a : α} {Γ Δ : List α} (h : Γ ⊆ Δ) : a :: Γ ⊆ a :: Δ :=
  List.cons_subset_cons a h

/-- **The replay** (Freund, proof of Theorem 6.5): an `LK` derivation of `Γ` gives, for every
assignment `f` of numerals to the free variables, a derivation of the embedded sequent at
height `Ω + h` and cut rank `Ω + m`, with `h`, `m` read off the derivation. -/
theorem replay (hX : XFreeL A) (hH : ThetaNote.Nice H) :
    ∀ {Γ : Sequent LXI} (d : ⊢ᴸᴷ¹ Γ) (f : ℕ → ℕ),
      IDerivable A (OmegaPlus (cutCx d)) H (OmegaPlus (hgt d)) (Γ.map (tr f))
  | _, Derivation.identity r v, f => by
    have hc : (tr f (Semiformula.rel r v)).freeVariables = ∅ := freeVariables_tr f _
    have d := taut (A := A) hH (tr f (Semiformula.rel r v)) hc
    rw [ThetaNote.adjoin_eq_self hH.isOperator (params_tr_sub hH f _)] at d
    have e : [Semiformula.rel r v, Semiformula.nrel r v].map (tr f) =
        [tr f (Semiformula.rel r v), ∼(tr f (Semiformula.rel r v))] := by
      rw [List.map_cons, List.map_cons, List.map_nil, ← tr_neg, Semiformula.neg_rel]
    rw [e]
    refine (d.mono_rank (ThetaNote.zero_le' _)).mono_height ?_ (OmegaPlus_mem hH _)
    show _ ≤ ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat 0)
    rw [ThetaNote.ofNat_zero, ThetaNote.nadd_zero]
    exact omegaMul_rk_tr_atom_le f r v
  | _, Derivation.verum, f => by
    rw [List.map_cons, List.map_nil, tr_verum]
    exact .verum (OmegaPlus_mem hH _) (paramsList_cons_sub (by simp) (by simp))
      List.mem_cons_self
  | _, Derivation.contraction d ss, f =>
    (replay hX hH d f).weaken_seq hH.isOperator (List.map_subset _ ss)
      (paramsList_map_tr hH f _)
  | _, @Derivation.or _ φ ψ Γ d, f => by
    have ih := replay hX hH d f
    rw [List.map_cons, List.map_cons] at ih
    have pD : params (tr f φ ⋎ tr f ψ) ⊆ H ∅ := by rw [← tr_or]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_or]
    set D := tr f φ ⋎ tr f ψ
    have pR := paramsList_map_tr hH f Γ
    have e1 : IDerivable A (OmegaPlus (cutCx d)) H (OmegaPlus (hgt d + 1))
        (tr f φ :: D :: Γ.map (tr f)) :=
      .orR (OmegaPlus_mem hH _) (paramsList_cons_sub (params_tr_sub hH f φ)
          (paramsList_cons_sub pD pR)) (List.mem_cons_of_mem _ List.mem_cons_self)
        (one_lt_OmegaPlus _) (OmegaPlus_lt (Nat.lt_succ_self _))
        (ih.weaken_seq hH.isOperator (by
          intro x hx; simp only [List.mem_cons] at hx ⊢; tauto)
          (paramsList_cons_sub (params_tr_sub hH f ψ) (paramsList_cons_sub
            (params_tr_sub hH f φ) (paramsList_cons_sub pD pR))))
    exact .orL (OmegaPlus_mem hH _) (paramsList_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt d + 1 < hgt d + 2 by omega)) e1
  | _, @Derivation.and _ φ Γ ψ dp dq, f => by
    have ihp := replay hX hH dp f
    have ihq := replay hX hH dq f
    rw [List.map_cons] at ihp ihq
    have pD : params (tr f φ ⋏ tr f ψ) ⊆ H ∅ := by rw [← tr_and]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_and]
    set D := tr f φ ⋏ tr f ψ
    have pR := paramsList_map_tr hH f Γ
    refine .and (OmegaPlus_mem hH _) (paramsList_cons_sub pD pR) List.mem_cons_self
      (OmegaPlus_lt (show hgt dp < max (hgt dp) (hgt dq) + 1 by omega))
      (OmegaPlus_lt (show hgt dq < max (hgt dp) (hgt dq) + 1 by omega)) ?_ ?_
    · refine (ihp.mono_rank (OmegaPlus_le (le_max_left _ _))).weaken_seq hH.isOperator
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsList_cons_sub (params_tr_sub hH f φ) (paramsList_cons_sub pD pR)
    · refine (ihq.mono_rank (OmegaPlus_le (le_max_right _ _))).weaken_seq hH.isOperator
        (subset_cons_cons (List.subset_cons_self _ _)) ?_
      exact paramsList_cons_sub (params_tr_sub hH f ψ) (paramsList_cons_sub pD pR)
  | _, @Derivation.all _ Γ φ d, f => by
    have pD : params (∀¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_all]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_all]
    set D := ∀¹ (numSubst₁ f ▹ embK φ)
    have pR := paramsList_map_tr hH f Γ
    refine .all (fun _ => OmegaPlus (hgt d)) (OmegaPlus_mem hH _) (paramsList_cons_sub pD pR)
      List.mem_cons_self (fun _ => OmegaPlus_lt (Nat.lt_succ_self _)) (fun n => ?_)
    have ih := replay hX hH d (n :>ₙ f)
    rw [List.map_cons, tr_free, tr_shifts] at ih
    refine ih.weaken_seq hH.isOperator (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsList_cons_sub ?_ (paramsList_cons_sub pD pR)
    rw [params_subst, params_rew]; exact (params_embK φ).trans
      (Set.singleton_subset_iff.mpr hH.Omega_mem)
  | _, @Derivation.exs _ φ t Γ d, f => by
    have ih := replay hX hH d f
    rw [List.map_cons, tr_subst] at ih
    have pD : params (∃¹ (numSubst₁ f ▹ embK φ)) ⊆ H ∅ := by
      rw [← tr_exs]; exact params_tr_sub hH f _
    rw [List.map_cons, tr_exs]
    set φ' := numSubst₁ f ▹ embK φ with hφ'
    set D := ∃¹ φ'
    have pR := paramsList_map_tr hH f Γ
    have ht : (numSubst f (embT t)).freeVariables = ∅ := freeVariables_numSubst_term' f _
    -- the witness is replaced by the numeral of its value
    have hsim := sim_subst_numI (φ := φ') (freeVariables_numSubst₁ f _)
      ((xFreeI_rew _ _).mpr (xFreeI_embK φ)) ht
    have ih' := ih.replace_head hX hH.isOperator hsim
    refine .exs (closedVal (numSubst f (embT t))) (OmegaPlus_mem hH _)
      (paramsList_cons_sub pD pR) List.mem_cons_self (ofNat_lt_OmegaPlus _ _)
      (OmegaPlus_lt (Nat.lt_succ_self _)) ?_
    refine ih'.weaken_seq hH.isOperator (subset_cons_cons (List.subset_cons_self _ _)) ?_
    refine paramsList_cons_sub ?_ (paramsList_cons_sub pD pR)
    rw [params_subst, hφ', params_rew]
    exact (params_embK φ).trans (Set.singleton_subset_iff.mpr hH.Omega_mem)
  | _, @Derivation.cut _ φ Γ Δ dp dn, f => by
    have ihp := replay hX hH dp f
    have ihn := replay hX hH dn f
    rw [List.map_cons] at ihp ihn
    rw [tr_neg] at ihn
    rw [List.map_append]
    have pR : paramsList (Γ.map (tr f) ++ Δ.map (tr f)) ⊆ H ∅ := by
      rw [paramsList_append]
      exact Set.union_subset (paramsList_map_tr hH f Γ) (paramsList_map_tr hH f Δ)
    have hρ : ∀ {j : ℕ}, j ≤ cutCx dp ∨ j ≤ cutCx dn →
        OmegaPlus j ≤ OmegaPlus (cutCx (Derivation.cut dp dn)) := by
      intro j hj
      refine OmegaPlus_le ?_
      show j ≤ max ((embK φ).complexity + 1) (max (cutCx dp) (cutCx dn))
      rcases hj with hj | hj <;> omega
    refine .cut (α₀ := OmegaPlus (max (hgt dp) (hgt dn))) (OmegaPlus_mem hH _) pR
      (rk_tr_lt f φ (le_max_left _ _)) (OmegaPlus_lt (Nat.lt_succ_self _)) ?_ ?_
    · refine ((ihp.mono_rank (hρ (Or.inl le_rfl))).mono_height
        (OmegaPlus_le (le_max_left _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.isOperator
        (subset_cons_cons (List.subset_append_left _ _)) ?_
      exact paramsList_cons_sub (params_tr_sub hH f φ) pR
    · refine ((ihn.mono_rank (hρ (Or.inr le_rfl))).mono_height
        (OmegaPlus_le (le_max_right _ _)) (OmegaPlus_mem hH _)).weaken_seq hH.isOperator
        (subset_cons_cons (List.subset_append_right _ _)) ?_
      exact paramsList_cons_sub (by rw [params_neg]; exact params_tr_sub hH f φ) pR

end Replay

/-! ### The axioms and their cut-away -/

section Main

variable {A : Semisentence LXI 1}

/-- **Every axiom of `ID1 A`** is derivable, cut-free, at a height `Ω · 2 + n` (Freund, proof
of Theorem 6.5). -/
theorem ax_derivable_of_mem (hA : Positive A) (hX : XFreeL A) {θ : Sentence LXI}
    (h : θ ∈ ID1 A) : AxDerivable A θ := by
  rcases (mem_ID1 A).mp h with h | h | h | rfl | ⟨F, rfl⟩
  · exact eq_axiom h
  · exact paMinus_axiom h
  · exact induction_axiom hX h
  · exact closure_axiom hX
  · exact indAx_axiom hA hX F

/-- A common height for finitely many axioms. -/
theorem axDerivable_list (Δ : List (Sentence LXI)) (h : ∀ θ ∈ Δ, AxDerivable A θ) :
    ∃ N : ℕ, ∀ θ ∈ Δ, ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
      IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat N))
        [(Rewriting.emb (embK θ) : Proposition LIinf)] := by
  induction Δ with
  | nil => exact ⟨0, fun θ hθ => absurd hθ (by simp)⟩
  | cons θ Δ ih =>
    obtain ⟨n, hn⟩ := h θ List.mem_cons_self
    obtain ⟨N, hN⟩ := ih fun θ' hθ' => h θ' (List.mem_cons_of_mem _ hθ')
    refine ⟨max n N, fun θ' hθ' H hH => ?_⟩
    have hmono : ∀ k, k ≤ max n N → ThetaNote.nadd OmegaTwo (ThetaNote.ofNat k) ≤
        ThetaNote.nadd OmegaTwo (ThetaNote.ofNat (max n N)) := fun k hk =>
      ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat hk)
    rcases List.mem_cons.mp hθ' with rfl | hθ'
    · exact (hn H hH).mono_height (hmono n (le_max_left _ _)) (OmegaTwo_mem hH _ _)
    · exact (hN θ' hθ' H hH).mono_height (hmono N (le_max_right _ _)) (OmegaTwo_mem hH _ _)

/-- A common bound for the complexities of finitely many embedded axioms. -/
theorem cx_list (Δ : List (Sentence LXI)) :
    ∃ m : ℕ, ∀ θ ∈ Δ, (embK θ).complexity + 1 ≤ m := by
  induction Δ with
  | nil => exact ⟨0, fun θ hθ => absurd hθ (by simp)⟩
  | cons θ Δ ih =>
    obtain ⟨m, hm⟩ := ih
    refine ⟨max ((embK θ).complexity + 1) m, fun θ' hθ' => ?_⟩
    rcases List.mem_cons.mp hθ' with rfl | hθ'
    · exact le_max_left _ _
    · exact le_trans (hm θ' hθ') (le_max_right _ _)

/-- **Cutting away the axioms**, one at a time (Freund, proof of Theorem 6.5): each cut is on
an embedded axiom of rank `≺ Ω + m`, against its derivation at height `Ω · 2 + N`. -/
theorem cut_axioms {H : Set ThetaNote → Set ThetaNote} (hH : ThetaNote.Nice H) {N m : ℕ} :
    ∀ (Δ : List (Sentence LXI)),
      (∀ θ ∈ Δ, IDerivable A ThetaNote.zero H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat N))
        [(Rewriting.emb (embK θ) : Proposition LIinf)]) →
      (∀ θ ∈ Δ, (embK θ).complexity + 1 ≤ m) →
      ∀ {h : ℕ} {Θ : Sequent LIinf}, N ≤ h → paramsList Θ ⊆ H ∅ →
        IDerivable A (OmegaPlus m) H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat h))
          (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf))) →
        IDerivable A (OmegaPlus m) H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat (h + Δ.length)))
          Θ
  | [], _, _, h, Θ, _, _, d => by simpa using d
  | θ :: Δ, hax, hcx, h, Θ, hNh, hΘ, d => by
    set φ : Proposition LIinf := Rewriting.emb (embK θ) with hφ
    have hO : {ThetaNote.Omega} ⊆ H ∅ := Set.singleton_subset_iff.mpr hH.Omega_mem
    have pφ : params φ ⊆ H ∅ := by rw [hφ, params_rew]; exact (params_embK θ).trans hO
    have pRest : paramsList (Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf)))
        ⊆ H ∅ := by
      intro x ⟨χ, hχ, hx⟩
      obtain ⟨θ', -, rfl⟩ := List.mem_map.mp hχ
      rw [params_neg, params_rew] at hx
      exact hO (params_embK θ' hx)
    have pΘR : paramsList (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf)))
        ⊆ H ∅ := by
      rw [paramsList_append]; exact Set.union_subset hΘ pRest
    have hL : IDerivable A (OmegaPlus m) H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat h))
        (∼φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf)))) :=
      d.weaken_seq hH.isOperator (by
        intro x hx
        simp only [List.map_cons, List.mem_append, List.mem_cons] at hx ⊢
        tauto) (paramsList_cons_sub (by rw [params_neg]; exact pφ) pΘR)
    have hR : IDerivable A (OmegaPlus m) H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat h))
        (φ :: (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf)))) :=
      (((hax θ List.mem_cons_self).mono_rank (ThetaNote.zero_le' _)).mono_height
        (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat hNh))
        (OmegaTwo_mem hH _ _)).weaken_seq hH.isOperator
        (List.cons_subset_cons _ (List.nil_subset _)) (paramsList_cons_sub pφ pΘR)
    have hrk : rk φ < OmegaPlus m := by
      rw [hφ, rk_rew]
      exact lt_of_le_of_lt (rk_le_Omega_nadd _) (OmegaPlus_lt (by
        have := hcx θ List.mem_cons_self; omega))
    have hcut : IDerivable A (OmegaPlus m) H (ThetaNote.nadd OmegaTwo (ThetaNote.ofNat (h + 1)))
        (Θ ++ Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf))) :=
      .cut (OmegaTwo_mem hH _ _) pΘR hrk
        (ThetaNote.nadd_ofNat_lt_nadd_ofNat _ (Nat.lt_succ_self h)) hR hL
    have key := cut_axioms hH Δ (fun θ' hθ' => hax θ' (List.mem_cons_of_mem _ hθ'))
      (fun θ' hθ' => hcx θ' (List.mem_cons_of_mem _ hθ')) (Nat.le_succ_of_le hNh) hΘ hcut
    rwa [show h + 1 + Δ.length = h + (θ :: Δ).length by simp; omega] at key

/-- **Freund, Theorem 6.5 (Embedding).**  If `ID1 A ⊢ σ`, then there are `m, n ∈ ℕ` such that
`H ⊢^{Ω·2+n}_{Ω+m} σ⁺` for every nice operator `H`; here `σ⁺` is the embedding with `X` read
as empty (`embK`), which is Freund's `σ⁺` for `X`-free `σ` (`embedding_theorem_xfree`).  The
operator form is positive (as in the source) and `X`-free. -/
theorem embedding_theorem (hA : Positive A) (hX : XFreeL A) {σ : Sentence LXI}
    (h : ID1 A ⊢ σ) :
    ∃ m n : ℕ, ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
      IDerivable A (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat m)) H
        (ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega) (ThetaNote.ofNat n))
        [(Rewriting.emb (embK σ) : Proposition LIinf)] := by
  obtain ⟨Δ, hΔ, ⟨d⟩⟩ := Theory.Proof.provable_iff.mp h
  have hax : ∀ θ ∈ Δ, AxDerivable A θ := fun θ hθ => ax_derivable_of_mem hA hX (hΔ θ hθ)
  obtain ⟨N, hN⟩ := axDerivable_list Δ hax
  obtain ⟨m0, hm0⟩ := cx_list Δ
  refine ⟨max (cutCx d) m0, max (hgt d) N + Δ.length, fun H hH => ?_⟩
  have r := replay hX hH d (fun _ => 0)
  have e : ((σ : Proposition LXI) :: ∼Sequent.embed Δ).map (tr (fun _ => 0)) =
      [(Rewriting.emb (embK σ) : Proposition LIinf)] ++
        Δ.map (fun θ => ∼(Rewriting.emb (embK θ) : Proposition LIinf)) := by
    rw [List.map_cons, tr_emb, List.singleton_append, List.tilde_def, Sequent.embed,
      List.map_map, List.map_map]
    congr 1
    refine List.map_congr_left fun θ _ => ?_
    simp only [Function.comp_apply, tr_neg, tr_emb]
  rw [e] at r
  refine cut_axioms hH Δ (fun θ hθ => hN θ hθ H hH)
    (fun θ hθ => le_trans (hm0 θ hθ) (le_max_right _ _)) (le_max_right _ _)
    (paramsList_cons_sub ((params_rew _ _).le.trans ((params_embK σ).trans
      (Set.singleton_subset_iff.mpr hH.Omega_mem))) (by simp)) ?_
  refine (r.mono_rank (OmegaPlus_le (le_max_left _ _))).mono_height ?_ (OmegaTwo_mem hH _ _)
  exact le_trans (ThetaNote.nadd_le_nadd_left' _ (ThetaNote.le_nadd_left _ _))
    (ThetaNote.nadd_le_nadd_right _ (ThetaNote.ofNat_le_ofNat (le_max_left _ _)))

/-- **Theorem 6.5 for `X`-free sentences**, in Freund's form: `H ⊢^{Ω·2+n}_{Ω+m} σ⁺` with
`σ⁺ = embed σ` (`I ↦ I^{≺Ω}`). -/
theorem embedding_theorem_xfree (hA : Positive A) (hX : XFreeL A) {σ : Sentence LXI}
    (hσ : XFreeL σ) (h : ID1 A ⊢ σ) :
    ∃ m n : ℕ, ∀ H : Set ThetaNote → Set ThetaNote, ThetaNote.Nice H →
      IDerivable A (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat m)) H
        (ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega) (ThetaNote.ofNat n))
        [embed (σ : Proposition LXI)] := by
  obtain ⟨m, n, hmn⟩ := embedding_theorem hA hX h
  refine ⟨m, n, fun H hH => ?_⟩
  have e : embed (σ : Proposition LXI) = (Rewriting.emb (embK σ) : Proposition LIinf) := by
    rw [embK_eq_embed hσ]; exact Semiformula.lMap_emb σ
  rw [e]; exact hmn H hH

/-- **Theorem 6.5 with the operator `H_0`**, the form the collapsing theorem consumes. -/
theorem embedding_theorem_Hop (hA : Positive A) (hX : XFreeL A) {σ : Sentence LXI}
    (h : ID1 A ⊢ σ) :
    ∃ m n : ℕ, IDerivable A (ThetaNote.nadd ThetaNote.Omega (ThetaNote.ofNat m))
      (ThetaNote.Hop ThetaNote.zero)
      (ThetaNote.nadd (ThetaNote.nadd ThetaNote.Omega ThetaNote.Omega) (ThetaNote.ofNat n))
      [(Rewriting.emb (embK σ) : Proposition LIinf)] := by
  obtain ⟨m, n, hmn⟩ := embedding_theorem hA hX h
  exact ⟨m, n, hmn _ (ThetaNote.Hop_nice ThetaNote.zero)⟩

end Main

end InductiveDef

end OrdinalAnalysis
