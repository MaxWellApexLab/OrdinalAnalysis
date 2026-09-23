/-
  The **full ω-model**, and
  soundness of the calculus of `LK.lean` in it.

  Foundation's `SecondOrder/Semantics.lean` supplies `Struc₂`, `Eval` and the
  per-constructor evaluation lemmas — and nothing else.  In particular it has
  **no substitution lemma of any kind**: no `eval_rew`, no `eval_bmap`, no
  analogue of the first-order `eval_free`/`eval_shift`, and nothing about the
  second-order substitution `φ/⟦ψ⟧`.  Without those, not one quantifier rule can
  be checked.  So the first half of this file is the missing calculus of
  substitution for the second-order semantics:

    `eval_rew`    first-order rewriting, mirroring `FirstOrder.…eval_rew`
    `eval_bmap`   renaming of bound *set* variables
    `eval_app`    a second-order substitution, the key one
    `eval_free₁`  the two `∀²`-rule lemmas, read off `eval_app`
    `eval_shift₁`
    `eval_subst₂` `Eval (φ/⟦ψ⟧) ↔ Eval φ [X ↦ {n | Eval ψ n}]`

  The second half is `stdSO`, the model with `M = ℕ`, arithmetic standard and
  **every** set of naturals available, and the soundness theorem: every
  derivation of `Γ` has, under every assignment of the free set and number
  variables, some member of `Γ` true.  Each axiom of `ACA` is then checked true
  in `stdSO` — `eval_setInduction` is `Nat.rec`, `eval_compAx` uses that every
  subset of `ℕ` is available, `eval_indScheme` is `Nat.rec` again, and the
  lifted `𝗘𝗤`/`𝗣𝗔⁻` sentences come from Foundation's `ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻` through
  `eval_lift` — giving `soundness_ACA : ACA ⊢ φ ⇒ ℕ ⊧ φ`, and with it the
  consistency of `ACA`.

  Soundness for `exs₂` needs the witness `{x | Eval ψ x}` to be an element of the
  family of sets; in the full model that is free, which is why the model is
  `Set.univ` and not, say, the arithmetical sets.  The `Arith ψ` side condition
  of `exs₂` is therefore *not* used here — it earns its keep in the ordinal
  analysis, not in the semantics.
-/
import OrdinalAnalysis.ACA.LK

set_option autoImplicit false

namespace OrdinalAnalysis.ACA

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open LO.SecondOrder.Semiproposition
open scoped LO.FirstOrder

/-! ### The missing substitution lemmas -/

section Substitution

variable {L : FirstOrder.Language} {Ξ ξ : Type*} {M : Type*} [s : FirstOrder.Structure L M]

/-- **First-order rewriting under the second-order `Eval`.**  Mirrors
`LO.FirstOrder.Semiformula.eval_rew`; the two set-atom cases are new. -/
theorem eval_rew {N : ℕ} {ξ₁ ξ₂ : Type*} {n₁ n₂ : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M}
    {E : Fin N → Set M} {e₂ : Fin n₂ → M} {f₂ : ξ₂ → M}
    (ω : FirstOrder.Rew L ξ₁ n₁ ξ₂ n₂) (φ : Semiformula L Ξ ξ₁ N n₁) :
    (ω ▹ φ).Eval 𝕊 F f₂ E e₂ ↔
      φ.Eval 𝕊 F (FirstOrder.Semiterm.val (s := s) e₂ f₂ ∘ ω ∘ FirstOrder.Semiterm.fvar) E
        (FirstOrder.Semiterm.val (s := s) e₂ f₂ ∘ ω ∘ FirstOrder.Semiterm.bvar) := by
  match φ with
  | .rel r v =>
      simp only [Semiformula.rew_rel_eq_comp, Semiformula.eval_rel]
      apply iff_of_eq; congr; funext i; simp [FirstOrder.Semiterm.val_rew]
  | .nrel r v =>
      simp only [Semiformula.rew_nrel, Semiformula.eval_nrel]
      apply iff_of_eq; congr 1; congr; funext i; simp [FirstOrder.Semiterm.val_rew]
  | t ∈# X => simp [FirstOrder.Semiterm.val_rew]
  | t ∉# X => simp [FirstOrder.Semiterm.val_rew]
  | t ∈& X => simp [FirstOrder.Semiterm.val_rew]
  | t ∉& X => simp [FirstOrder.Semiterm.val_rew]
  | ⊤ => simp
  | ⊥ => simp
  | φ ⋏ ψ => simp [eval_rew ω φ, eval_rew ω ψ]
  | φ ⋎ ψ => simp [eval_rew ω φ, eval_rew ω ψ]
  | ∀¹ φ =>
      simpa [Function.comp_def, eval_rew ω.q φ] using
        iff_of_eq <| forall_congr fun x ↦ by congr; funext i; cases i using Fin.cases <;> simp
  | ∃¹ φ =>
      simpa [Function.comp_def, eval_rew ω.q φ] using
        exists_congr fun x ↦ iff_of_eq <| by
          congr; funext i; cases i using Fin.cases <;> simp
  | ∀² φ => simp [eval_rew ω φ]
  | ∃² φ => simp [eval_rew ω φ]

/-- **Renaming of bound set variables under `Eval`.** -/
theorem eval_bmap {N₁ N₂ n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M}
    {E : Fin N₂ → Set M} {e : Fin n → M} {f : ξ → M}
    (g : Fin N₁ → Fin N₂) (φ : Semiformula L Ξ ξ N₁ n) :
    (φ.bmap g).Eval 𝕊 F f E e ↔ φ.Eval 𝕊 F f (E ∘ g) e := by
  match φ with
  | .rel r v => simp
  | .nrel r v => simp
  | t ∈# X => simp
  | t ∉# X => simp
  | t ∈& X => simp
  | t ∉& X => simp
  | ⊤ => simp
  | ⊥ => simp
  | φ ⋏ ψ => simp [eval_bmap g φ, eval_bmap g ψ]
  | φ ⋎ ψ => simp [eval_bmap g φ, eval_bmap g ψ]
  | ∀¹ φ => simp [eval_bmap g φ]
  | ∃¹ φ => simp [eval_bmap g φ]
  | ∀² φ =>
      simp only [Semiformula.bmap_all₁, Semiformula.eval_fal₁, eval_bmap (Fin.retrusion g) φ]
      refine forall_congr' fun X => forall_congr' fun _ => ?_
      have : (X :> E) ∘ Fin.retrusion g = X :> (E ∘ g) := by
        funext i; cases i using Fin.cases <;> simp
      rw [this]
  | ∃² φ =>
      simp only [Semiformula.bmap_exs₁, Semiformula.eval_exs₁, eval_bmap (Fin.retrusion g) φ]
      refine exists_congr fun X => and_congr_right fun _ => ?_
      have : (X :> E) ∘ Fin.retrusion g = X :> (E ∘ g) := by
        funext i; cases i using Fin.cases <;> simp
      rw [this]


/-! The two bookkeeping identities the `∀²`/`∃²` cases of `eval_app` need: under
`Ω.q` the *new* set variable reads as the freshly quantified set, and every old
one reads exactly as it did under `Ω`. -/

private theorem cons_comp_succ {N₂ : ℕ} (X : Set M) (E : Fin N₂ → Set M) :
    (X :> E) ∘ Fin.succ = E := by funext i; simp

private theorem q_fv_eq {N₁ N₂ : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M}
    {E : Fin N₂ → Set M} {f : ξ → M} {Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ} {X : Set M} :
    (fun Y => {x | ((SecondOrder.Rew.q Ω).fv Y).Eval 𝕊 F f (X :> E) ![x]}) =
      (fun Y => {x | (Ω.fv Y).Eval 𝕊 F f E ![x]}) := by
  funext Y
  ext x
  simp only [Set.mem_ofPred_eq, SecondOrder.Rew.q_fv, eval_bmap, cons_comp_succ]

private theorem q_bv_eq {N₁ N₂ : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M}
    {E : Fin N₂ → Set M} {f : ξ → M} {Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ} {X : Set M} :
    (fun Y => {x | ((SecondOrder.Rew.q Ω).bv Y).Eval 𝕊 F f (X :> E) ![x]}) =
      X :> (fun Y => {x | (Ω.bv Y).Eval 𝕊 F f E ![x]}) := by
  funext Y
  cases Y using Fin.cases with
  | zero => ext x; simp
  | succ Y =>
      ext x
      simp only [Matrix.cons_val_succ, Set.mem_ofPred_eq, SecondOrder.Rew.q_bv_succ, eval_bmap,
        cons_comp_succ]


/-- **A second-order substitution under `Eval`.**  Applying `Ω` to `φ` is the
same as evaluating `φ` with each set variable `X` read as the set defined by the
formula `Ω` assigns to it.  This is the lemma Foundation does not have, and
without it neither `all₂` nor `exs₂` can be checked. -/
theorem eval_app {N₁ N₂ n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M}
    {E : Fin N₂ → Set M} {e : Fin n → M} {f : ξ → M}
    (Ω : SecondOrder.Rew L Ξ N₁ Ξ N₂ ξ) (φ : Semiformula L Ξ ξ N₁ n) :
    (Ω.app φ).Eval 𝕊 F f E e ↔
      φ.Eval 𝕊 (fun X => {x | (Ω.fv X).Eval 𝕊 F f E ![x]}) f
        (fun X => {x | (Ω.bv X).Eval 𝕊 F f E ![x]}) e := by
  match φ with
  | .rel r v => simp
  | .nrel r v => simp
  | t ∈# X =>
      have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.fvar) = f := by funext y; simp
      have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.bvar) = ![t.val e f] := by funext i; simp
      simp only [SecondOrder.Rew.app_bvar, eval_rew, h1, h2, Semiformula.eval_bvar,
        Set.mem_ofPred_eq]
  | t ∉# X =>
      have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.fvar) = f := by funext y; simp
      have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.bvar) = ![t.val e f] := by funext i; simp
      simp only [SecondOrder.Rew.app_nbvar, LogicalConnective.HomClass.map_neg, eval_rew, h1, h2,
        Semiformula.eval_nbvar, Set.mem_ofPred_eq]
      exact Iff.rfl
  | t ∈& X =>
      have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.fvar) = f := by funext y; simp
      have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.bvar) = ![t.val e f] := by funext i; simp
      simp only [SecondOrder.Rew.app_fvar, eval_rew, h1, h2, Semiformula.eval_fvar,
        Set.mem_ofPred_eq]
  | t ∉& X =>
      have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.fvar) = f := by funext y; simp
      have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
          FirstOrder.Semiterm.bvar) = ![t.val e f] := by funext i; simp
      simp only [SecondOrder.Rew.app_nfvar, LogicalConnective.HomClass.map_neg, eval_rew, h1, h2,
        Semiformula.eval_nfvar, Set.mem_ofPred_eq]
      exact Iff.rfl
  | ⊤ => simp
  | ⊥ => simp
  | φ ⋏ ψ => simp [eval_app Ω φ, eval_app Ω ψ]
  | φ ⋎ ψ => simp [eval_app Ω φ, eval_app Ω ψ]
  | ∀¹ φ => simp [eval_app Ω φ]
  | ∃¹ φ => simp [eval_app Ω φ]
  | ∀² φ =>
      simp only [SecondOrder.Rew.app_all₁, Semiformula.eval_fal₁]
      refine forall_congr' fun X => forall_congr' fun _ => ?_
      rw [eval_app (SecondOrder.Rew.q Ω) φ, q_fv_eq (Ω := Ω) (X := X) (E := E) (f := f),
        q_bv_eq (Ω := Ω) (X := X) (E := E) (f := f)]
  | ∃² φ =>
      simp only [SecondOrder.Rew.app_exs₁, Semiformula.eval_exs₁]
      refine exists_congr fun X => and_congr_right fun _ => ?_
      rw [eval_app (SecondOrder.Rew.q Ω) φ, q_fv_eq (Ω := Ω) (X := X) (E := E) (f := f),
        q_bv_eq (Ω := Ω) (X := X) (E := E) (f := f)]


/-! ### The four rule-shaped corollaries -/

/-- **The `∃²` rule's substitution lemma.**  `φ/⟦ψ⟧` is `φ` read with its set
variable interpreted as the set that `ψ` defines. -/
@[simp] theorem eval_subst₂ {𝕊 : Set (Set M)} {F : ℕ → Set M} {f : ℕ → M}
    (φ : Semiproposition L 1 0) (ψ : Semiformula L ℕ ℕ 0 1) :
    (φ/⟦ψ⟧).Eval 𝕊 F f ![] ![] ↔
      φ.Eval 𝕊 F f ![{x | ψ.Eval 𝕊 F f ![] ![x]}] ![] := by
  have hfv : (fun X => {x | ((SecondOrder.Rew.subst ![ψ]).fv X).Eval 𝕊 F f
      (![] : Fin 0 → Set M) ![x]}) = F := by
    funext X; ext x; simp
  have hbv : (fun X => {x | ((SecondOrder.Rew.subst ![ψ]).bv X).Eval 𝕊 F f
      (![] : Fin 0 → Set M) ![x]}) = ![{x | ψ.Eval 𝕊 F f ![] ![x]}] := by
    funext X
    have hX : (SecondOrder.Rew.subst ![ψ]).bv X = ψ := by
      simp only [SecondOrder.Rew.subst_bv]
      exact Matrix.cons_val_fin_one _ _ X
    rw [hX, Matrix.cons_val_fin_one]
  show ((SecondOrder.Rew.subst ![ψ]).app φ).Eval 𝕊 F f ![] ![] ↔ _
  rw [eval_app, hfv, hbv]

/-- **The `∀²` rule's eigenvariable lemma.**  `free₁` moves the outermost bound
set variable into the free set variable `0`. -/
@[simp] theorem eval_free₁ {N n : ℕ} {𝕊 : Set (Set M)} {F : ℕ → Set M} {E : Fin N → Set M}
    {f : ξ → M} {e : Fin n → M} {A : Set M} (φ : Semiformula L ℕ ξ (N + 1) n) :
    ((SecondOrder.Rew.free).app φ).Eval 𝕊 (A :>ₙ F) f E e ↔ φ.Eval 𝕊 F f (E <: A) e := by
  have hfv : (fun X => {x | ((SecondOrder.Rew.free (L := L) (ξ := ξ) (N := N)).fv X).Eval 𝕊
      (A :>ₙ F) f E ![x]}) = F := by
    funext X; ext x; simp
  have hbv : (fun Y => {x | ((SecondOrder.Rew.free (L := L) (ξ := ξ) (N := N)).bv Y).Eval 𝕊
      (A :>ₙ F) f E ![x]}) = E <: A := by
    funext Y
    cases Y using Fin.lastCases with
    | last => ext x; simp
    | cast Y => ext x; simp
  rw [eval_app, hfv, hbv]

/-- **The `∀²` rule's context lemma.**  `shift₁` renumbers the free set
variables so that `0` is free for the eigenvariable. -/
@[simp] theorem eval_shift₁ {N n : ℕ} {𝕊 : Set (Set M)} {F : ℕ → Set M} {E : Fin N → Set M}
    {f : ξ → M} {e : Fin n → M} {A : Set M} (φ : Semiformula L ℕ ξ N n) :
    ((SecondOrder.Rew.shift).app φ).Eval 𝕊 (A :>ₙ F) f E e ↔ φ.Eval 𝕊 F f E e := by
  have hfv : (fun X => {x | ((SecondOrder.Rew.shift (L := L) (ξ := ξ) (N := N)).fv X).Eval 𝕊
      (A :>ₙ F) f E ![x]}) = F := by
    funext X; ext x; simp
  have hbv : (fun Y => {x | ((SecondOrder.Rew.shift (L := L) (ξ := ξ) (N := N)).bv Y).Eval 𝕊
      (A :>ₙ F) f E ![x]}) = E := by
    funext Y; ext x; simp
  rw [eval_app, hfv, hbv]

/-- **The `∀¹` rule's eigenvariable lemma.** -/
@[simp] theorem eval_free₀ {N n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {E : Fin N → Set M}
    {f : ℕ → M} {e : Fin n → M} {a : M} (φ : Semiformula L Ξ ℕ N (n + 1)) :
    (FirstOrder.Rewriting.free φ : Semiformula L Ξ ℕ N n).Eval 𝕊 F (a :>ₙ f) E e ↔
      φ.Eval 𝕊 F f E (e <: a) := by
  have h1 : (FirstOrder.Semiterm.val (s := s) e (a :>ₙ f) ∘ (FirstOrder.Rew.free) ∘
      FirstOrder.Semiterm.fvar) = f := by funext x; simp
  have h2 : (FirstOrder.Semiterm.val (s := s) e (a :>ₙ f) ∘ (FirstOrder.Rew.free) ∘
      FirstOrder.Semiterm.bvar) = e <: a := by
    funext i; cases i using Fin.lastCases <;> simp
  rw [show (FirstOrder.Rewriting.free φ : Semiformula L Ξ ℕ N n) = FirstOrder.Rew.free ▹ φ from rfl,
    eval_rew, h1, h2]

/-- **The `∀¹` rule's context lemma.** -/
@[simp] theorem eval_shift₀ {N n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {E : Fin N → Set M}
    {f : ℕ → M} {e : Fin n → M} {a : M} (φ : Semiformula L Ξ ℕ N n) :
    (FirstOrder.Rewriting.shift φ : Semiformula L Ξ ℕ N n).Eval 𝕊 F (a :>ₙ f) E e ↔
      φ.Eval 𝕊 F f E e := by
  have h1 : (FirstOrder.Semiterm.val (s := s) e (a :>ₙ f) ∘ (FirstOrder.Rew.shift) ∘
      FirstOrder.Semiterm.fvar) = f := by funext x; simp
  have h2 : (FirstOrder.Semiterm.val (s := s) e (a :>ₙ f) ∘
      (FirstOrder.Rew.shift : FirstOrder.Rew L ℕ n ℕ n) ∘ FirstOrder.Semiterm.bvar) = e := by
    funext i; simp
  rw [show (FirstOrder.Rewriting.shift φ : Semiformula L Ξ ℕ N n) = FirstOrder.Rew.shift ▹ φ from rfl,
    eval_rew, h1, h2]

/-- **The `∃¹` rule's substitution lemma.** -/
@[simp] theorem eval_subst₁ {N n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {E : Fin N → Set M}
    {f : ξ → M} {e : Fin n → M} (φ : Semiformula L Ξ ξ N 1)
    (t : FirstOrder.Semiterm L ξ n) :
    (φ/[t]).Eval 𝕊 F f E e ↔ φ.Eval 𝕊 F f E ![t.val e f] := by
  have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
      FirstOrder.Semiterm.fvar) = f := by funext y; simp
  have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst ![t]) ∘
      FirstOrder.Semiterm.bvar) = ![t.val e f] := by funext i; simp
  rw [show (φ/[t]) = FirstOrder.Rew.subst ![t] ▹ φ from rfl, eval_rew, h1, h2]

/-- **Simultaneous substitution of a term vector under `Eval`** — the
`n`-parameter generalisation of `eval_subst₁`, which is what the standard
(parametrized) induction scheme needs. -/
theorem eval_subst {N n₁ n₂ : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {E : Fin N → Set M}
    {f : ξ → M} {e : Fin n₂ → M} (φ : Semiformula L Ξ ξ N n₁)
    (v : Fin n₁ → FirstOrder.Semiterm L ξ n₂) :
    (FirstOrder.Rew.subst v ▹ φ).Eval 𝕊 F f E e ↔
      φ.Eval 𝕊 F f E (fun i => (v i).val e f) := by
  have h1 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst v) ∘
      FirstOrder.Semiterm.fvar) = f := by funext y; simp
  have h2 : (FirstOrder.Semiterm.val (s := s) e f ∘ (FirstOrder.Rew.subst v) ∘
      FirstOrder.Semiterm.bvar) = fun i => (v i).val e f := by funext i; simp
  rw [eval_rew, h1, h2]

/-! ### The universal closures under `Eval`

Only the direction "true under every assignment of the closed slots ⇒ the
closure is true" is needed (the axioms are *proved* true, never used as
hypotheses), and it is the direction that goes through with no bookkeeping. -/

/-- **`∀¹*` is true if the matrix is true under every number assignment.** -/
theorem eval_allNums_of {N : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M}
    {E : Fin N → Set M} :
    ∀ (n : ℕ) (φ : Semiformula L Ξ ξ N n),
      (∀ e : Fin n → M, φ.Eval 𝕊 F f E e) → (∀¹* φ).Eval 𝕊 F f E ![]
  |       0, _, h => h ![]
  | (n + 1), φ, h =>
      eval_allNums_of n (∀¹ φ) fun e => by
        simp only [Semiformula.eval_fal₀]
        intro x
        exact h (x :> e)

/-- **`∀²*` is true if the matrix is true under every assignment of sets from
`𝕊` to the closed slots.** -/
theorem eval_allSets_of {n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {f : ξ → M}
    {e : Fin n → M} :
    ∀ (N : ℕ) (φ : Semiformula L Ξ ξ N n),
      (∀ E : Fin N → Set M, (∀ i, E i ∈ 𝕊) → φ.Eval 𝕊 F f E e) → (∀²* φ).Eval 𝕊 F f ![] e
  |       0, _, h => h ![] fun i => i.elim0
  | (N + 1), φ, h =>
      eval_allSets_of N (∀² φ) fun E hE => by
        simp only [Semiformula.eval_fal₁]
        intro X hX
        refine h (X :> E) fun i => ?_
        cases i using Fin.cases with
        | zero => simpa using hX
        | succ i => simpa using hE i

/-- **Lifted first-order formulas evaluate as they do first-order.** -/
theorem eval_lift {N n : ℕ} {𝕊 : Set (Set M)} {F : Ξ → Set M} {E : Fin N → Set M}
    {f : ξ → M} {e : Fin n → M} (φ : FirstOrder.Semiformula L ξ n) :
    (lift φ : Semiformula L Ξ ξ N n).Eval 𝕊 F f E e ↔ FirstOrder.Semiformula.Eval e f φ := by
  induction φ using FirstOrder.Semiformula.rec' <;> simp [*]

end Substitution

/-! ### Soundness

`Derivation.sound` is proved for an arbitrary `ℒₒᵣ`-structure with **every**
subset available as a value of the set quantifiers.  Only the `exs₂` case uses
that; and it uses it in the cheapest possible way, since the witness
`{x | Eval ψ x}` is always in `Set.univ`.  The `Arith ψ` side condition of
`exs₂` is therefore not consumed here — it pays off in the ordinal analysis. -/

namespace Derivation

variable {M : Type*} [FirstOrder.Structure ℒₒᵣ M]

set_option maxHeartbeats 1000000 in
/-- **Soundness of the calculus in a full model**, for every assignment of the
free set variables and the free number variables. -/
theorem sound {Γ : SecondOrder.Sequent ℒₒᵣ} (d : Derivation Γ) :
    ∀ (F : ℕ → Set M) (f : ℕ → M), ∃ φ ∈ Γ, φ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by
  induction d with
  | @identity φ =>
      intro F f
      by_cases h : φ.Eval (Set.univ : Set (Set M)) F f ![] ![]
      · exact ⟨φ, by simp, h⟩
      · exact ⟨∼φ, by simp, by simpa using h⟩
  | @cut φ Γ _ _ ihp ihn =>
      intro F f
      have hp : φ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
          ∃ ψ ∈ Γ, ψ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ihp F f
      have hn : ¬φ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
          ∃ ψ ∈ Γ, ψ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ihn F f
      rcases hp with h | ⟨ψ, hψ, hv⟩
      · rcases hn with hnn | ⟨ψ, hψ, hv⟩
        · exact absurd h hnn
        · exact ⟨ψ, hψ, hv⟩
      · exact ⟨ψ, hψ, hv⟩
  | wk _ hsub ih =>
      intro F f
      obtain ⟨φ, hφ, hv⟩ := ih F f
      exact ⟨φ, hsub hφ, hv⟩
  | verum => intro F f; exact ⟨⊤, by simp, by simp⟩
  | @and φ ψ Γ _ _ ihp ihq =>
      intro F f
      have hp : φ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
          ∃ χ ∈ Γ, χ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ihp F f
      rcases hp with hp | ⟨χ, hχ, hv⟩
      · have hq : ψ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
            ∃ χ ∈ Γ, χ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ihq F f
        rcases hq with hq | ⟨χ, hχ, hv⟩
        · exact ⟨φ ⋏ ψ, by simp, by simp [hp, hq]⟩
        · exact ⟨χ, by simp [hχ], hv⟩
      · exact ⟨χ, by simp [hχ], hv⟩
  | @or φ ψ Γ _ ih =>
      intro F f
      have h : φ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
          ψ.Eval (Set.univ : Set (Set M)) F f ![] ![] ∨
          ∃ χ ∈ Γ, χ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ih F f
      rcases h with h | h | ⟨χ, hχ, hv⟩
      · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
      · exact ⟨φ ⋎ ψ, by simp, by simp [h]⟩
      · exact ⟨χ, by simp [hχ], hv⟩
  | @all₁ φ Γ _ ih =>
      intro F f
      by_cases hΓ : ∃ ψ ∈ Γ, ψ.Eval (Set.univ : Set (Set M)) F f ![] ![]
      · obtain ⟨ψ, hψ, hv⟩ := hΓ
        exact ⟨ψ, by simp [hψ], hv⟩
      · refine ⟨∀¹ φ, by simp, ?_⟩
        simp only [Semiformula.eval_fal₀]
        intro a
        obtain ⟨χ, hχ, hv⟩ := ih F (a :>ₙ f)
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · simpa using hv
        · exfalso
          have hχ'' : χ ∈ Γ.map Semiproposition.shift₀ := hχ'
          obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ''
          exact hΓ ⟨ψ, hψ, by simpa using hv⟩
  | @exs₁ φ t Γ _ ih =>
      intro F f
      have h : φ.Eval (Set.univ : Set (Set M)) F f ![] ![t.val ![] f] ∨
          ∃ χ ∈ Γ, χ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ih F f
      rcases h with h | ⟨χ, hχ, hv⟩
      · exact ⟨∃¹ φ, by simp, ⟨t.val ![] f, h⟩⟩
      · exact ⟨χ, by simp [hχ], hv⟩
  | @all₂ φ Γ _ ih =>
      intro F f
      by_cases hΓ : ∃ ψ ∈ Γ, ψ.Eval (Set.univ : Set (Set M)) F f ![] ![]
      · obtain ⟨ψ, hψ, hv⟩ := hΓ
        exact ⟨ψ, by simp [hψ], hv⟩
      · refine ⟨∀² φ, by simp, ?_⟩
        simp only [Semiformula.eval_fal₁]
        intro A _
        obtain ⟨χ, hχ, hv⟩ := ih (A :>ₙ F) f
        rcases List.mem_cons.mp hχ with rfl | hχ'
        · simpa using hv
        · exfalso
          have hχ'' : χ ∈ Γ.map Semiproposition.shift₁ := hχ'
          obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ''
          exact hΓ ⟨ψ, hψ, by simpa using hv⟩
  | @exs₂ φ ψ Γ _ _ ih =>
      intro F f
      have h : φ.Eval (Set.univ : Set (Set M)) F f
            ![{x | ψ.Eval (Set.univ : Set (Set M)) F f ![] ![x]}] ![] ∨
          ∃ χ ∈ Γ, χ.Eval (Set.univ : Set (Set M)) F f ![] ![] := by simpa using ih F f
      rcases h with h | ⟨χ, hχ, hv⟩
      · exact ⟨∃² φ, by simp, ⟨_, Set.mem_univ _, h⟩⟩
      · exact ⟨χ, by simp [hχ], hv⟩

end Derivation

/-! ### The full ω-model -/

/-- **The full second-order model of arithmetic**: the standard model of `ℒₒᵣ`
on `ℕ`, with *every* set of naturals a value of the set quantifiers. -/
def stdSO : Struc₂ ℒₒᵣ := Struc₂.of (Set.univ : Set (Set ℕ)) ℒₒᵣ

@[simp] theorem stdSO_sets : stdSO.sets = (Set.univ : Set (Set ℕ)) := rfl

@[simp] theorem stdSO_dom : stdSO.Dom = ℕ := rfl


/-- Truth in the full ω-model, under every assignment of the free set and number
variables — i.e. truth of the universal closure. -/
def SOTrue (φ : Proposition ℒₒᵣ) : Prop :=
  ∀ (F : ℕ → Set ℕ) (f : ℕ → ℕ), φ.Eval (Set.univ : Set (Set ℕ)) F f ![] ![]

theorem soTrue_iff {φ : Proposition ℒₒᵣ} :
    SOTrue φ ↔ ∀ (F : ℕ → Set ℕ) (f : ℕ → ℕ), φ.Eval stdSO.sets F f ![] ![] := Iff.rfl

/-! ### Every axiom of `ACA` is true in the full ω-model -/

/-- **The set induction axiom is true.**  It is `Nat.rec`, once the syntax is
peeled off. -/
theorem eval_setInduction : SOTrue setInduction := by
  intro F f
  simp only [setInduction, Semiformula.eval_fal₁, LogicalConnective.HomClass.map_imply,
    LogicalConnective.HomClass.map_and, Semiformula.eval_bvar, Semiformula.eval_fal₀]
  intro X _ h x
  obtain ⟨h0, hs⟩ := h
  simp only [zeroT, succT, Matrix.cons_val_zero] at h0 hs ⊢
  simp only [FirstOrder.Semiterm.val_bvar, Matrix.cons_val_fin_one] at h0 hs ⊢
  induction x with
  | zero => simpa using h0
  | succ n ih => simpa using hs n (by simpa using ih)

/-- **Set extensionality is true.**  `eval_lift` reduces the equality atom to
ordinary equality of naturals; the rest is `Eq.mpr`. -/
theorem eval_setExt : SOTrue setExt := by
  intro F f
  simp only [setExt, Semiformula.eval_fal₁, Semiformula.eval_fal₀,
    LogicalConnective.HomClass.map_imply, eval_lift]
  intro X _ x y hxy hx
  simp only [Semiformula.eval_bvar, FirstOrder.Semiterm.val_bvar, Matrix.cons_val_fin_one] at hx ⊢
  have hxy' : y = x := hxy
  subst hxy'
  exact hx

/-- **Every `∀²`-closed comprehension axiom is true** in the full model —
including the non-arithmetical ones, since every subset of `ℕ` is available.
`ACA₀` only takes the arithmetical `NoSetFvar` instances, but truth does not
care. -/
theorem eval_arithComp₂ {N n : ℕ} (ψ : Semiproposition ℒₒᵣ N (n + 1)) :
    SOTrue (arithComp₂ ψ) := by
  intro F f
  refine eval_allSets_of N _ fun E _ => eval_allNums_of n _ fun e => ?_
  show (compBody ψ).Eval (Set.univ : Set (Set ℕ)) F f E e
  simp only [compBody, Semiformula.eval_exs₁]
  refine ⟨{x | ψ.Eval (Set.univ : Set (Set ℕ)) F f E (x :> e)}, Set.mem_univ _, ?_⟩
  simp only [Semiformula.eval_fal₀]
  intro x
  have hE : (({x | ψ.Eval (Set.univ : Set (Set ℕ)) F f E (x :> e)} :> E) :
      Fin (N + 1) → Set ℕ) ∘ Fin.succ = E := by
    funext i; simp
  simp [LogicalConnective.HomClass.map_iff, LogicalConnective.Prop.iff_eq,
    Semiformula.eval_bvar, eval_bmap, hE]

/-- The value of the base-case substitution: `#0 ↦ 0`, the parameters
unchanged. -/
private theorem val_indZeroSub (n : ℕ) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    (fun i => FirstOrder.Semiterm.val (M := ℕ) e f (indZeroSub n i)) = (0 : ℕ) :> e := by
  funext i
  cases i using Fin.cases with
  | zero => simp [indZeroSub, zeroT]
  | succ i => simp [indZeroSub]

/-- The value of the successor-step substitution: `#0 ↦ x + 1`, the parameters
unchanged. -/
private theorem val_indSuccSub (n : ℕ) (x : ℕ) (e : Fin n → ℕ) (f : ℕ → ℕ) :
    (fun i => FirstOrder.Semiterm.val (M := ℕ) (x :> e) f (indSuccSub n i)) = (x + 1) :> e := by
  funext i
  cases i using Fin.cases with
  | zero => simp [indSuccSub, succT]
  | succ i => simp [indSuccSub]

/-- **Every universally closed induction axiom is true**, for an arbitrary
second-order `φ` with arbitrary set and number parameters.  This is the axiom
that separates `ACA` from `ACA₀`; semantically it costs nothing. -/
theorem eval_indScheme₂ {N n : ℕ} (φ : Semiproposition ℒₒᵣ N (n + 1)) :
    SOTrue (indScheme₂ φ) := by
  intro F f
  refine eval_allSets_of N _ fun E _ => eval_allNums_of n _ fun e => ?_
  show (indBody φ).Eval (Set.univ : Set (Set ℕ)) F f E e
  simp only [indBody, LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_fal₀, eval_subst, val_indZeroSub, val_indSuccSub]
  rintro ⟨h0, hs⟩ x
  induction x with
  | zero => exact h0
  | succ m ih => exact hs m ih

/-- **A first-order sentence true in `ℕ` lifts to a true proposition.** -/
theorem eval_liftSentence {σ : FirstOrder.Sentence ℒₒᵣ}
    (h : FirstOrder.Semiformula.Eval (M := ℕ) ![] Empty.elim σ) : SOTrue (liftSentence σ) := by
  intro F f
  have : (lift (FirstOrder.Rewriting.emb σ) : Proposition ℒₒᵣ).Eval
      (Set.univ : Set (Set ℕ)) F f ![] ![] := by
    rw [eval_lift]; simpa using h
  exact this

/-- The lifted equality axioms are true. -/
theorem eval_eqAxioms {χ : Proposition ℒₒᵣ} (h : χ ∈ eqAxioms) : SOTrue χ := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact eval_liftSentence (LO.FirstOrder.models_iff.mp (LO.FirstOrder.models_of_mem hσ))

/-- The lifted `PA⁻` axioms are true. -/
theorem eval_paMinus {χ : Proposition ℒₒᵣ} (h : χ ∈ paMinus) : SOTrue χ := by
  obtain ⟨σ, hσ, rfl⟩ := h
  exact eval_liftSentence (LO.FirstOrder.models_iff.mp (LO.FirstOrder.models_of_mem hσ))

/-- **Every axiom of `ACA₀` is true in the full ω-model.** -/
theorem eval_ACA₀ {χ : Proposition ℒₒᵣ} (h : χ ∈ ACA₀) : SOTrue χ := by
  rcases h with ((h | h) | rfl | rfl) | ⟨N, n, ψ, _, _, _, rfl⟩
  · exact eval_eqAxioms h
  · exact eval_paMinus h
  · exact eval_setInduction
  · exact eval_setExt
  · exact eval_arithComp₂ ψ

/-- **Every axiom of `ACA` is true in the full ω-model.** -/
theorem eval_ACA {χ : Proposition ℒₒᵣ} (h : χ ∈ ACA) : SOTrue χ := by
  rcases h with h | ⟨N, n, φ, _, _, rfl⟩
  · exact eval_ACA₀ h
  · exact eval_indScheme₂ φ

/-! ### Soundness of the theories -/

/-- **Soundness of a schema whose axioms are all true.** -/
theorem soundness_of {𝓢 : Set (Proposition ℒₒᵣ)} (h𝓢 : ∀ χ ∈ 𝓢, SOTrue χ)
    {φ : Proposition ℒₒᵣ} (h : Provable 𝓢 φ) : SOTrue φ := by
  obtain ⟨Γ, hΓ, ⟨d⟩⟩ := provable_iff.mp h
  intro F f
  obtain ⟨χ, hχ, hv⟩ := d.sound F f
  rcases List.mem_cons.mp hχ with rfl | hχ'
  · exact hv
  · exfalso
    have hχ'' : χ ∈ Γ.map (∼·) := hχ'
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hχ''
    have hneg : ¬ψ.Eval (Set.univ : Set (Set ℕ)) F f ![] ![] := by simpa using hv
    exact hneg (h𝓢 ψ (hΓ ψ hψ) F f)

/-- **`ACA₀` is sound for the full ω-model.** -/
theorem soundness_ACA₀ {φ : Proposition ℒₒᵣ} (h : Provable ACA₀ φ) : SOTrue φ :=
  soundness_of (fun _ hχ => eval_ACA₀ hχ) h

/-- **`ACA ⊢ φ ⇒ ℕ ⊧ φ`** — the theorem this file exists for. -/
theorem soundness_ACA {φ : Proposition ℒₒᵣ} (h : Provable ACA φ) : SOTrue φ :=
  soundness_of (fun _ hχ => eval_ACA hχ) h

/-- **`ACA` is consistent.** -/
theorem not_provable_falsum : ¬Provable ACA ⊥ := by
  intro h
  have := soundness_ACA h (fun _ => ∅) (fun _ => 0)
  simp at this

/-- **`ACA₀` is consistent.** -/
theorem not_provable_falsum₀ : ¬Provable ACA₀ ⊥ := fun h =>
  not_provable_falsum (aca_provable_mono h)

end OrdinalAnalysis.ACA
