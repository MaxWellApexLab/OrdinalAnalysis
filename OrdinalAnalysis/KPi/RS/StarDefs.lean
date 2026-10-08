import OrdinalAnalysis.KPi.RS.Infty

/-!
# The RS calculus, part 5: the system `RS*` (B92 Definitions 2.1--2.3)

`Star R σ Γ` is `⊢*_σ Γ`: derivations built from the four rules of B92 Definition 2.2

* `(⋀)*`  : `all`,
* `(⋁)*`  : `ex`, with the side condition `k(ι₀,..,ιₙ) ⊆ k(Γ, ⋁(A_ι))*`,
* `(Ad)*` : `ad`,  `Γ, Ad(a) → B(a)` from `Γ, B(L_κ)` (`κ ≤ |a|`, `κ ∈ R`),
* `(Ref)*`: `ref`, the axiom scheme `Γ, A → ∃z∈L_κ A^{(z,κ)}` (`A ∈ Σ(κ)`, `κ ∈ R`),
* `(Found)*`: `found`, the axiom scheme `Γ, ∃x∈L_α(∀y∈x A(y) ∧ ¬A(x)), ∀x∈L_α A(x)`.

The index `σ` is the bound `ρ` of Definition 2.3: every principal formula of an `(Ad)*` has rank `< σ`,
and `(Ref)*`, `(Found)*` are allowed only for `σ > 0`.  Hence `Star R 0 Γ` is B92's `⊢* Γ`
(derivable by `(⋀)*` and `(⋁)*` alone).

Sequents are *sets* of RS-sentences (as in the spike and in `RS^∞`, B92 Def. 3.1).  A B92 multiset
derivation gives a set derivation by forgetting multiplicities; the calculus here is what the later
stages use.
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-! ### `k` of sequents and the star operation -/

/-- `k(Γ)`. -/
def kSeq (Γ : Set RSS) : Set Ordinal.{1} := {ξ | ∃ A ∈ Γ, ξ ∈ A.k}

open Classical in
/-- `ξ^R` (B92 Def. 1.12). -/
noncomputable def powR (R : Set Ordinal.{1}) (ξ : Ordinal.{1}) : Ordinal.{1} :=
  if _ : ∃ κ ∈ R, ξ < κ then sInf {κ | κ ∈ R ∧ ξ < κ} else ξ

/-- `X* := X ∪ {ω} ∪ {ξ+1 : ξ ∈ X} ∪ {ξ^R : ξ ∈ X}` (B92 Def 2.1 (2)). -/
def starK (R : Set Ordinal.{1}) (X : Set Ordinal.{1}) : Set Ordinal.{1} :=
  X ∪ {ω} ∪ (fun ξ => ξ + 1) '' X ∪ (powR R) '' X

theorem subset_starK (R : Set Ordinal.{1}) (X : Set Ordinal.{1}) : X ⊆ starK R X :=
  fun _ h => Or.inl (Or.inl (Or.inl h))

theorem starK_mono (R : Set Ordinal.{1}) {X Y : Set Ordinal.{1}} (h : X ⊆ Y) :
    starK R X ⊆ starK R Y := by
  rintro ξ (((hx | hx) | ⟨y, hy, rfl⟩) | ⟨y, hy, rfl⟩)
  · exact Or.inl (Or.inl (Or.inl (h hx)))
  · exact Or.inl (Or.inl (Or.inr hx))
  · exact Or.inl (Or.inr ⟨y, h hy, rfl⟩)
  · exact Or.inr ⟨y, h hy, rfl⟩

theorem kSeq_mono {Γ Δ : Set RSS} (h : Γ ⊆ Δ) : kSeq Γ ⊆ kSeq Δ :=
  fun _ ⟨A, hA, hξ⟩ => ⟨A, h hA, hξ⟩

theorem k_sub_kSeq {Γ : Set RSS} {A : RSS} (h : A ∈ Γ) : A.k ⊆ kSeq Γ :=
  fun _ hξ => ⟨A, h, hξ⟩

/-! ### renaming of variables in `D0` (used to state `(Found)*` and the instances of the schemes) -/

/-- `Fin.snoc`-style extension of a variable map over one new innermost variable. -/
def liftF {m k : ℕ} (f : Fin m → Fin k) : Fin (m + 1) → Fin (k + 1) :=
  ext (fun i => (f i).castSucc) (Fin.last k)

@[simp] theorem liftF_last {m k : ℕ} (f : Fin m → Fin k) : liftF f (Fin.last m) = Fin.last k := by
  simp [liftF]

@[simp] theorem liftF_castSucc {m k : ℕ} (f : Fin m → Fin k) (i : Fin m) :
    liftF f i.castSucc = (f i).castSucc := by
  simp [liftF]

def Bd.rename {m k : ℕ} (f : Fin m → Fin k) : Bd m → Bd k
  | .var i => .var (f i)
  | .lev α => .lev α

/-- rename the free variables of a `D0` formula. -/
def D0.rename : {m k : ℕ} → (Fin m → Fin k) → D0 m → D0 k
  | _, _, f, .mem i j => .mem (f i) (f j)
  | _, _, f, .nmem i j => .nmem (f i) (f j)
  | _, _, f, .ad i => .ad (f i)
  | _, _, f, .nad i => .nad (f i)
  | _, _, f, .and A B => .and (D0.rename f A) (D0.rename f B)
  | _, _, f, .or A B => .or (D0.rename f A) (D0.rename f B)
  | _, _, f, .bex b A => .bex (b.rename f) (D0.rename (liftF f) A)
  | _, _, f, .ball b A => .ball (b.rename f) (D0.rename (liftF f) A)

theorem ext_comp_liftF {m k : ℕ} {X : Sort _} (e : Fin k → X) (x : X) (f : Fin m → Fin k) :
    (ext e x) ∘ liftF f = ext (e ∘ f) x := by
  funext i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp

theorem D0.rename_neg : ∀ {m k : ℕ} (f : Fin m → Fin k) (A : D0 m),
    (A.rename f).neg = A.neg.rename f
  | _, _, f, .mem i j => rfl
  | _, _, f, .nmem i j => rfl
  | _, _, f, .ad i => rfl
  | _, _, f, .nad i => rfl
  | _, _, f, .and A B => by simp [D0.rename, D0.neg, D0.rename_neg f A, D0.rename_neg f B]
  | _, _, f, .or A B => by simp [D0.rename, D0.neg, D0.rename_neg f A, D0.rename_neg f B]
  | _, _, f, .bex b A => by simp [D0.rename, D0.neg, D0.rename_neg (liftF f) A]
  | _, _, f, .ball b A => by simp [D0.rename, D0.neg, D0.rename_neg (liftF f) A]

theorem kBd_rename {m k : ℕ} (f : Fin m → Fin k) (b : Bd m) (e : Fin k → Set Ordinal.{1}) :
    kBd (b.rename f) e = kBd b (e ∘ f) := by
  cases b <;> rfl

theorem kD_rename : ∀ {m k : ℕ} (f : Fin m → Fin k) (A : D0 m) (e : Fin k → Set Ordinal.{1}),
    kD (A.rename f) e = kD A (e ∘ f)
  | _, _, f, .mem i j, e => rfl
  | _, _, f, .nmem i j, e => rfl
  | _, _, f, .ad i, e => rfl
  | _, _, f, .nad i, e => rfl
  | _, _, f, .and A B, e => by simp [D0.rename, kD, kD_rename f A, kD_rename f B]
  | _, _, f, .or A B, e => by simp [D0.rename, kD, kD_rename f A, kD_rename f B]
  | _, _, f, .bex b A, e => by
      simp only [D0.rename, kD, kBd_rename, kD_rename (liftF f) A, ext_comp_liftF]
  | _, _, f, .ball b A, e => by
      simp only [D0.rename, kD, kBd_rename, kD_rename (liftF f) A, ext_comp_liftF]

/-! ### the sentences of `(Found)*` -/

/-- `∃x∈L_α(∀y∈x A(y) ∧ ¬A(x))` for `A(x)` with parameters `ρ` (`x` is the last variable of `A`).
The variable map sends the parameters to themselves and `x` to the new bound variable `y`. -/
def foundE (α : Ordinal.{1}) {n : ℕ} (A : D0 (n + 1)) : D0 n :=
  .bex (.lev α) (.and (.ball (.var (Fin.last n))
      (D0.rename (ext (fun i : Fin n => i.castSucc.castSucc) (Fin.last (n + 1))) A)) A.neg)

/-- `∀x∈L_α A(x)`. -/
def foundU (α : Ordinal.{1}) {n : ℕ} (A : D0 (n + 1)) : D0 n :=
  .ball (.lev α) A

/-! ### `RS*` -/

/-- `⊢*_σ Γ` (B92 Def 2.2/2.3). -/
inductive Star (R : Set Ordinal.{1}) : Ordinal.{1} → Set RSS → Prop
  | all {A : RSS} {Γ : Set RSS} {σ : Ordinal.{1}} (hA : (expand R A).isOr = false)
      (h : ∀ j : (expand R A).J, Star R σ (insert ((expand R A).child j) Γ)) :
      Star R σ (insert A Γ)
  | ex {A : RSS} {Γ : Set RSS} {σ : Ordinal.{1}} (js : Set (expand R A).J) (hfin : js.Finite)
      (hA : (expand R A).isOr = true)
      (hk : ∀ j ∈ js, (expand R A).ks j ⊆ starK R (kSeq (insert A Γ)))
      (h : Star R σ (Γ ∪ ((expand R A).child '' js))) :
      Star R σ (insert A Γ)
  | ad {n : ℕ} {i : Fin n} (B : D0 n) {Γ : Set RSS} {σ : Ordinal.{1}} (ρ : Fin n → T)
      (h : ∀ κ : AdIdx R (ρ i),
        Star R σ (insert (RSS.base B (Function.update ρ i (T.L κ.1))) Γ))
      (hr : (RSS.base B ρ).rk < σ) :
      Star R σ (insert (RSS.base (D0.or (D0.nad i) B) ρ) Γ)
  | ref {κ : Ordinal.{1}} (S : SigmaData κ) (hκ : κ ∈ R) {Γ : Set RSS} {σ : Ordinal.{1}}
      (hσ : 0 < σ) :
      Star R σ (insert (RSS.or S.sentence.neg S.refl) Γ)
  | found (α : Ordinal.{1}) {n : ℕ} (A : D0 (n + 1)) (ρ : Fin n → T) {Γ : Set RSS}
      {σ : Ordinal.{1}} (hσ : 0 < σ) :
      Star R σ (insert (RSS.base (foundE α A) ρ) (insert (RSS.base (foundU α A) ρ) Γ))

variable {R : Set Ordinal.{1}}

/-- weakening. -/
theorem Star.mono {σ : Ordinal.{1}} {Γ : Set RSS} (h : Star R σ Γ) : ∀ {Δ : Set RSS}, Γ ⊆ Δ →
    Star R σ Δ := by
  induction h with
  | @all A Γ σ hA h ih =>
    intro Δ hΔ
    have hAΔ : A ∈ Δ := hΔ (Set.mem_insert _ _)
    have hΓ : Γ ⊆ Δ := fun x hx => hΔ (Set.mem_insert_of_mem _ hx)
    have := Star.all (Γ := Δ) hA (fun j => ih j (Set.insert_subset_insert hΓ))
    rwa [Set.insert_eq_of_mem hAΔ] at this
  | @ex A Γ σ js hfin hA hk h ih =>
    intro Δ hΔ
    have hAΔ : A ∈ Δ := hΔ (Set.mem_insert _ _)
    have hΓ : Γ ⊆ Δ := fun x hx => hΔ (Set.mem_insert_of_mem _ hx)
    have := Star.ex (Γ := Δ) js hfin hA
      (fun j hj => (hk j hj).trans (starK_mono R (kSeq_mono (Set.insert_subset_insert hΓ))))
      (ih (Set.union_subset_union_left _ hΓ))
    rwa [Set.insert_eq_of_mem hAΔ] at this
  | @ad n i B Γ σ ρ h hr ih =>
    intro Δ hΔ
    have hAΔ : RSS.base (D0.or (D0.nad i) B) ρ ∈ Δ := hΔ (Set.mem_insert _ _)
    have hΓ : Γ ⊆ Δ := fun x hx => hΔ (Set.mem_insert_of_mem _ hx)
    have := Star.ad (Γ := Δ) B ρ (fun κ => ih κ (Set.insert_subset_insert hΓ)) hr
    rwa [Set.insert_eq_of_mem hAΔ] at this
  | @ref κ S hκ Γ σ hσ =>
    intro Δ hΔ
    have hAΔ : RSS.or S.sentence.neg S.refl ∈ Δ := hΔ (Set.mem_insert _ _)
    have := Star.ref (R := R) (Γ := Δ) (σ := σ) S hκ hσ
    rwa [Set.insert_eq_of_mem hAΔ] at this
  | @found α n A ρ Γ σ hσ =>
    intro Δ hΔ
    have h1 : RSS.base (foundE α A) ρ ∈ Δ := hΔ (Set.mem_insert _ _)
    have h2 : RSS.base (foundU α A) ρ ∈ Δ := hΔ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have := Star.found (R := R) (Γ := Δ) (σ := σ) α A ρ hσ
    rwa [Set.insert_eq_of_mem h2, Set.insert_eq_of_mem h1] at this

/-- monotonicity in the bound `σ`. -/
theorem Star.mono_sigma {σ σ' : Ordinal.{1}} {Γ : Set RSS} (h : Star R σ Γ) (hσ : σ ≤ σ') :
    Star R σ' Γ := by
  induction h with
  | all hA h ih => exact Star.all hA (fun j => ih j hσ)
  | ex js hfin hA hk h ih => exact Star.ex js hfin hA hk (ih hσ)
  | ad B ρ h hr ih => exact Star.ad B ρ (fun κ => ih κ hσ) (lt_of_lt_of_le hr hσ)
  | ref S hκ hσ0 => exact Star.ref S hκ (lt_of_lt_of_le hσ0 hσ)
  | found α A ρ hσ0 => exact Star.found α A ρ (lt_of_lt_of_le hσ0 hσ)

/-! ### ambient-set forms of the rules -/

theorem Star.all' {A : RSS} {Δ : Set RSS} {σ : Ordinal.{1}} (hAΔ : A ∈ Δ)
    (hA : (expand R A).isOr = false)
    (h : ∀ j : (expand R A).J, Star R σ (insert ((expand R A).child j) Δ)) : Star R σ Δ := by
  have := Star.all (Γ := Δ) hA h
  rwa [Set.insert_eq_of_mem hAΔ] at this

theorem Star.ex' {A : RSS} {Δ : Set RSS} {σ : Ordinal.{1}} (hAΔ : A ∈ Δ)
    (js : Set (expand R A).J) (hfin : js.Finite) (hA : (expand R A).isOr = true)
    (hk : ∀ j ∈ js, (expand R A).ks j ⊆ starK R (kSeq Δ))
    (h : Star R σ (Δ ∪ ((expand R A).child '' js))) : Star R σ Δ := by
  have := Star.ex (Γ := Δ) js hfin hA (by rwa [Set.insert_eq_of_mem hAΔ]) h
  rwa [Set.insert_eq_of_mem hAΔ] at this

/-- one witness of a `⋁`. -/
theorem Star.ex1' {A : RSS} {Δ : Set RSS} {σ : Ordinal.{1}} (hAΔ : A ∈ Δ)
    (j : (expand R A).J) (hA : (expand R A).isOr = true)
    (hk : (expand R A).ks j ⊆ starK R (kSeq Δ))
    (h : Star R σ (insert ((expand R A).child j) Δ)) : Star R σ Δ := by
  refine Star.ex' hAΔ {j} (Set.finite_singleton _) hA ?_ ?_
  · intro j' hj'
    have : j' = j := hj'
    subst this
    exact hk
  · rw [Set.image_singleton, Set.union_singleton]
    exact h

end OrdinalAnalysis.KPi.RS
