/-
  The climb, second-order: transfinite induction along a coded ordering is
  derivable in the evaluating calculus `ACA_∞`.

  `Gentzen/Climb.lean` and `Gentzen/ClimbVeblen.lean`, transposed to Foundation's
  monadic second-order syntax and merged into one file, because in the second
  order the two halves are much shorter than they were.

  * The climb itself is unchanged.  To derive `X(n̄)` one opens `¬Prog(X)` at
    `n`, which asks for `X(k̄)` for every `k ≺ n` (each obtained recursively) and
    for `¬X(n̄)` — and *that* is where the first-order file used the atomic
    identity axiom `of_mem_identity` while here the general identity of
    `Calculus.lean` supplies it at height `0` for the atom `n̄ ∈& 0`.  The ω-rule
    collects the `k`, and one step of the climb costs four successors.

  * The false instances are supplied **generically**.  In the first order,
    `ClimbEpsilon0.lean` and `ClimbVeblen.lean` each had to run ω-completeness
    by hand and then transport the height along `ofNONote`, because ω-completeness
    lived in `NONote`.  `ACAOmega/OmegaTruth₂.lean` is already generic in the
    height system, so `neg_precAt₂_derivable` holds for *every* `CodedOrder₂ O`
    at the height `ofNat (complexity of ≺)` — no height map, no per-instance work.
    The three facts it consumes are all fields of `CodedOrder₂`: the ordering is
    a lift (hence `SetFree`), its first-order original is closed (hence
    `NumClosed`), and `trueN₂_precAt` reads it in `ℕ`.

  * The instance is `gamma0Order₂`: the *unsegmented* coded Veblen ordering of
    all of `Gamma0Note`.  `ClimbVeblen.lean`'s bookkeeping reappears as
    `height_lt_veblenNote`: the climb to a notation below `φ_a(b)` stays below
    `φ_a(b)` for `0 < a`, since `φ_a(b)` is closed under `ω ^ ·`, the natural
    sum, `1` and the finite notations (`Ordinal/Veblen/VeblenBelow.lean`).  The
    `ε` case is `a = 1`.

  The file closes with the axiom the `Γ₀` station adds: for every `a`,

      TIupto(≺₁, ā) :≡ Prog(≺₁, X) → ∀ x ≺₁ ā, x ∈ X

  is cut-free derivable at height `ω^(a ⊕ 1) + 1`, hence below `ε_{a⊕1}`, hence
  below `Γ₀`.  This is `Gentzen/Epsilon1Axiom.lean`'s `TI₀_derivable_at` with the
  fixed cut-off `ε₀` made a parameter: the ω-rule takes the supremum of the
  climbs to the notations below `ā`, and `height_lt` bounds every one of them by
  `ω^(a ⊕ 1)`.

  `c₂` is `irreducible_def`, as `ClimbVeblen.c₁` is: with a transparent `def`
  the elaborator unfolds the whole of `precFO₁` when it meets the complexity
  inside an ordinal expression, and hangs — with no error message and no
  heartbeat, because the loop is inside the kernel's `whnf`.

  Contents.

    `neg_precAt₂_derivable`          the false instances, for every `CodedOrder₂`
    `ClimbData₂`                     the data of a climb
    `ClimbData₂.core`                **one step**
    `ClimbData₂.height`, `height_lt` the heights
    `ClimbData₂.code`, `nonimage`, `climb`   **the climb**
    `c₂`, `K₂`, `gamma0Climb₂`       the instance at `gamma0Order₂`
    `height_lt_veblenNote`, `height_lt_epsilonNote`   the closure
    `TIupto₂_derivable_at`, `TIupto₂_derivable`, `TIupto₂_derivable_lt`
                                     **the new axiom, below `Γ₀`**
-/
import OrdinalAnalysis.ACAOmega.SubstX₂
import OrdinalAnalysis.ACAOmega.OmegaTruth₂
import OrdinalAnalysis.ACAOmega.Gamma0Order₂

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace OrdinalAnalysis.ACAOmega.Climb₂

open LO LO.SecondOrder
open LO.SecondOrder.Semiformula
open scoped LO.FirstOrder
open OrdinalAnalysis.ACA
open OrdinalAnalysis.Gentzen.CodedVeblen (precN₁ precN₁_dom lt_of_precN₁_code)
open OrdinalAnalysis.Gentzen.VNoteBridge (gamma0Code)
open Ordinal

variable {O : Type} [LinearOrder O] [WellFoundedLT O] [OrdinalNotation O]

/-- Cut-free derivability in the evaluating second-order calculus. -/
abbrev D₂ (α : O) (Γ : SecondOrder.Sequent ℒₒᵣ) : Prop :=
  OmegaDerivable₂ trueArithLits₂ evInst₂ 0 α Γ

/-! ### The false instances of `≺`, for every coded ordering

A false comparison at two numerals is a closed, set-free proposition false in
`ℕ`; ω-completeness derives its negation at the height of its complexity, which
is the complexity of the ordering itself — uniformly in `k` and `n`. -/

/-- **`∼(k̄ ≺ n̄)` is derivable whenever `k ≺ n` fails**, at the height
`ofNat (complexity of ≺)`, in any height system. -/
theorem neg_precAt₂_derivable (C : CodedOrder₂ O) {k n : ℕ} (h : ¬ C.precN k n) :
    D₂ (OrdinalNotation.ofNat C.prec.complexity : O)
      [ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n)))] := by
  have hS : SetFree (precAt₂ C.prec (numAt k) (numAt n) : Proposition ℒₒᵣ) :=
    setFree_precAt₂ C.prec C.setFree_prec _ _
  have hprec : OmegaTruth₂.NumClosed C.prec := by
    rw [C.prec_eq]
    exact OmegaTruth₂.numClosed_lift C.freeVariables_prec₀
  have hc : OmegaTruth₂.NumClosed (precAt₂ C.prec (numAt k) (numAt n) : Proposition ℒₒᵣ) :=
    OmegaTruth₂.numClosed_rew
      (FirstOrder.Rew.subst ![(numAt k : FirstOrder.SyntacticTerm ℒₒᵣ), numAt n]) hprec
      (Fin.forall_fin_two.mpr ⟨by simp, by simp⟩)
  have hf : ¬ TrueN₂ (precAt₂ C.prec (numAt k) (numAt n) : Proposition ℒₒᵣ) := by
    rw [C.trueN₂_precAt k n]
    exact h
  have hd := OmegaTruth₂.omega_complete₂_ev_neg (O := O) _ hS hc hf
  have ec : (precAt₂ C.prec (numAt k) (numAt n) : Proposition ℒₒᵣ).complexity
      = C.prec.complexity :=
    OmegaTruth₂.complexity_rew₂ _ C.prec
  have e : (OmegaTruth₂.hgt₂ (precAt₂ C.prec (numAt k) (numAt n) : Proposition ℒₒᵣ) : O)
      = OrdinalNotation.ofNat C.prec.complexity :=
    congrArg (OrdinalNotation.ofNat (O := O)) ec
  rwa [e] at hd

/-! ### The data of a climb -/

/-- **The data of a climb** along the coded ordering `C`: a height `K` at which
every false instance of `≺` is derivable, below every `ω^(a ⊕ 1)` together with
`1`; and the domain property of `≺`.

`neg_precAt₂_derivable` discharges the second field for every `CodedOrder₂`; the
two order-arithmetic fields and `dom` are what the instances supply. -/
structure ClimbData₂ (C : CodedOrder₂ O) where
  /-- The height at which every false instance of `≺` is derivable. -/
  K : O
  /-- …and the derivations. -/
  neg_precAt : ∀ {k n : ℕ}, ¬ C.precN k n →
    D₂ K [ev₂ (∼(precAt₂ C.prec (numAt k) (numAt n)))]
  /-- `K` is below every `ω^(a ⊕ 1)`. -/
  K_lt : ∀ a : O, K < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one)
  /-- …and so is `1`. -/
  one_lt : ∀ a : O,
    OrdinalNotation.one < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one)
  /-- Both sides of a true comparison are codes of notations. -/
  dom : ∀ {k n : ℕ}, C.precN k n → (∃ o : O, C.code o = k) ∧ (∃ o : O, C.code o = n)

namespace ClimbData₂

variable {C : CodedOrder₂ O}

/-- The height of the climb at `o`. -/
def height (M : ClimbData₂ C) (o : O) : O :=
  OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
    (OrdinalNotation.nadd
      (OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one)) M.K))))

/-! ### One step of the climb -/

set_option maxHeartbeats 2000000 in
/-- **One step.**  If `k̄ ∈ X` is derivable for every `k ≺ n` at height `δ`, and
`δ` is at least `K`, then `n̄ ∈ X` is derivable at height `δ + 4`. -/
theorem core (M : ClimbData₂ C) (n : ℕ) (δ : O) (hδ : M.K ≤ δ)
    (H : ∀ k, C.precN k n → D₂ δ [ev₂ (∼(Prog₂ C.prec)), xat k]) :
    D₂ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
        (OrdinalNotation.succ δ))))
      [ev₂ (∼(Prog₂ C.prec)), xat n] := by
  -- the instances of `∀ y ≺ n̄, y ∈ X`
  have hprem : ∀ k, D₂ (OrdinalNotation.succ δ)
      (evInst₂.inst (ev₂ (belowBody₂ C n)) k :: [ev₂ (∼(Prog₂ C.prec)), xat n]) := by
    intro k
    rw [inst_belowBody₂, ev₂_precOrXat₂_eq]
    refine OmegaDerivable₂.or (OrdinalNotation.lt_succ δ) ?_
    by_cases hk : C.precN k n
    · refine OmegaDerivable₂.contraction ?_ (H k hk)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl rfl)
    · refine OmegaDerivable₂.contraction ?_ ((M.neg_precAt hk).mono_ord hδ)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl
      exact Or.inl rfl
  have hbelow : D₂ (OrdinalNotation.succ (OrdinalNotation.succ δ))
      (ev₂ (belowAt₂ C n) :: [ev₂ (∼(Prog₂ C.prec)), xat n]) := by
    rw [ev₂_belowAt₂_eq]
    exact OmegaDerivable₂.omegaRule (fun _ => OrdinalNotation.succ δ)
      (fun _ => OrdinalNotation.lt_succ _) hprem
  -- general identity closes `n̄ ∉ X`
  have hneg : D₂ δ (nxat n :: [ev₂ (∼(Prog₂ C.prec)), xat n]) :=
    OmegaDerivable₂.of_mem_identity (xat n)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
      List.mem_cons_self
  have hP : D₂ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ δ)))
      (ev₂ (P₂ C n) :: [ev₂ (∼(Prog₂ C.prec)), xat n]) := by
    rw [ev₂_P₂_eq]
    exact OmegaDerivable₂.and (OrdinalNotation.lt_succ _)
      (OrdinalNotation.lt_succ_of_le
        ((OrdinalNotation.le_succ _).trans (OrdinalNotation.le_succ _))) hbelow hneg
  have hexs : D₂ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
      (OrdinalNotation.succ δ))))
      ((∃¹ (ev₂ ((below₂ C.prec) ⋏ ((#0 : FirstOrder.Semiterm ℒₒᵣ ℕ 1) ∉& 0))))
        :: [ev₂ (∼(Prog₂ C.prec)), xat n]) := by
    refine OmegaDerivable₂.exs n (OrdinalNotation.lt_succ _) ?_
    rw [inst_negProg₂_body]
    exact hP
  refine OmegaDerivable₂.drop_head hexs ?_
  rw [← ev₂_negProg₂_eq]
  exact List.mem_cons_self

/-! ### The heights -/

/-- The step of the heights: `height o' < ω^(o ⊕ 1)` for `o' < o`. -/
theorem height_lt (M : ClimbData₂ C) {o o' : O} (hlt : o' < o) :
    M.height o' < OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one) := by
  have hw : OrdinalNotation.omegaPow (OrdinalNotation.nadd o' OrdinalNotation.one)
      < OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one) :=
    OrdinalNotation.omegaPow_lt_omegaPow (OrdinalNotation.nadd_lt_nadd_left _ hlt)
  have hK := M.K_lt o
  have h1 := M.one_lt o
  simp only [height, OrdinalNotation.succ]
  exact OrdinalNotation.nadd_lt_omegaPow (OrdinalNotation.nadd_lt_omegaPow
    (OrdinalNotation.nadd_lt_omegaPow (OrdinalNotation.nadd_lt_omegaPow
      (OrdinalNotation.nadd_lt_omegaPow hw hK) h1) h1) h1) h1

theorem K_le_base (M : ClimbData₂ C) (o : O) :
    M.K ≤ OrdinalNotation.nadd
      (OrdinalNotation.omegaPow (OrdinalNotation.nadd o OrdinalNotation.one)) M.K :=
  OrdinalNotation.le_nadd_right _ _

/-! ### The climb -/

/-- **The climb along the codes.**  For the code of `o`, height `height o`. -/
theorem code (M : ClimbData₂ C) :
    ∀ o : O, D₂ (M.height o) [ev₂ (∼(Prog₂ C.prec)), xat (C.code o)] := by
  intro o
  refine WellFoundedLT.induction (motive := fun o =>
    D₂ (M.height o) [ev₂ (∼(Prog₂ C.prec)), xat (C.code o)]) o ?_
  intro o ih
  refine M.core (C.code o) _ (M.K_le_base o) (fun k hk => ?_)
  obtain ⟨o', rfl⟩ := (M.dom hk).1
  have hlt : o' < o := C.lt_of_precN_code hk
  refine (ih o' hlt).mono_ord (le_of_lt ?_)
  exact lt_of_lt_of_le (M.height_lt hlt) (OrdinalNotation.le_nadd_left _ _)

/-- A number that codes nothing has no predecessors, so its climb is one step. -/
theorem nonimage (M : ClimbData₂ C) (n : ℕ) (hn : ¬ ∃ o : O, C.code o = n) :
    D₂ (OrdinalNotation.succ (OrdinalNotation.succ (OrdinalNotation.succ
        (OrdinalNotation.succ M.K))))
      [ev₂ (∼(Prog₂ C.prec)), xat n] :=
  M.core n M.K le_rfl (fun _ hk => absurd (M.dom hk).2 hn)

/-- **The climb.**  `∼Prog(≺, X), n̄ ∈ X` is derivable for every `n`. -/
theorem climb (M : ClimbData₂ C) (n : ℕ) :
    ∃ α : O, D₂ α [ev₂ (∼(Prog₂ C.prec)), xat n] := by
  by_cases h : ∃ o : O, C.code o = n
  · obtain ⟨o, rfl⟩ := h
    exact ⟨_, M.code o⟩
  · exact ⟨_, M.nonimage n h⟩

end ClimbData₂

/-! ### The instance: the unsegmented coded Veblen ordering -/

/-- The complexity of the coded Veblen ordering, as a second-order formula;
every instance `k̄ ≺₁ n̄` has it. -/
irreducible_def c₂ : ℕ := gamma0Order₂.prec.complexity

/-- The height at which every false instance of `≺₁` is derivable. -/
def K₂ : Gamma0Note := OrdinalNotation.ofNat c₂

theorem K₂_eq : K₂ = (OrdinalNotation.ofNat gamma0Order₂.prec.complexity : Gamma0Note) := by
  unfold K₂
  rw [c₂_def]

theorem K₂_eq_ofNat : K₂ = Gamma0Note.ofNat c₂ := rfl

/-! #### Ordinal facts -/

theorem repr_omegaPow_one : Gamma0Note.repr (Gamma0Note.omegaPow 1) = ω := by
  rw [Gamma0Note.repr_omegaPow, Gamma0Note.repr_one, opow_one]

theorem omegaPow_one_le_omegaPow_nadd_one (a : Gamma0Note) :
    Gamma0Note.omegaPow 1 ≤ Gamma0Note.omegaPow (Gamma0Note.nadd a 1) :=
  Gamma0Note.omegaPow_le_omegaPow (Gamma0Note.le_nadd_right a 1)

/-- `K₂ < ω^(a ⊕ 1)`: `K₂` is finite and `ω ≤ ω^(a ⊕ 1)`. -/
theorem K₂_lt (a : Gamma0Note) :
    K₂ < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one) := by
  show K₂ < Gamma0Note.omegaPow (Gamma0Note.nadd a 1)
  refine lt_of_lt_of_le ?_ (omegaPow_one_le_omegaPow_nadd_one a)
  rw [K₂_eq_ofNat, Gamma0Note.lt_def, Gamma0Note.repr_ofNat, repr_omegaPow_one]
  exact natCast_lt_omega0 c₂

/-- `1 < ω^(a ⊕ 1)` for every `a`. -/
theorem one_lt₂ (a : Gamma0Note) :
    OrdinalNotation.one
      < OrdinalNotation.omegaPow (OrdinalNotation.nadd a OrdinalNotation.one) := by
  show (1 : Gamma0Note) < Gamma0Note.omegaPow (Gamma0Note.nadd a 1)
  refine lt_of_lt_of_le ?_ (omegaPow_one_le_omegaPow_nadd_one a)
  rw [Gamma0Note.lt_def, Gamma0Note.repr_one, repr_omegaPow_one]
  exact one_lt_omega0

/-! #### The false instances of `≺₁` -/

theorem neg_precAt₂_gamma0 {k n : ℕ} (h : ¬ precN₁ k n) :
    D₂ K₂ [ev₂ (∼(precAt₂ gamma0Order₂.prec (numAt k) (numAt n)))] := by
  rw [K₂_eq]
  exact neg_precAt₂_derivable gamma0Order₂ h

/-- **The data of the climb along `≺₁`**, with heights in the Veblen notations. -/
def gamma0Climb₂ : ClimbData₂ gamma0Order₂ where
  K := K₂
  neg_precAt := fun h => neg_precAt₂_gamma0 h
  K_lt := K₂_lt
  one_lt := one_lt₂
  dom := fun h => precN₁_dom h

@[simp] theorem gamma0Climb₂_K : gamma0Climb₂.K = K₂ := rfl

/-- **The climb along `≺₁`.**  `∼Prog(≺₁, X), n̄ ∈ X` is derivable for every `n`,
at some height below `Γ₀`. -/
theorem gamma0_climb (n : ℕ) :
    ∃ α : Gamma0Note, D₂ α [ev₂ (∼(Prog₂ gamma0Order₂.prec)), xat n] :=
  gamma0Climb₂.climb n

/-- The explicit height for a code. -/
theorem gamma0_climb_code (o : Gamma0Note) :
    D₂ (gamma0Climb₂.height o)
      [ev₂ (∼(Prog₂ gamma0Order₂.prec)), xat (gamma0Code o)] :=
  gamma0Climb₂.code o

/-! ### The closure of the heights

The climb to a notation below `φ_a(b)` stays below `φ_a(b)` whenever `0 < a`: it
is a natural sum of `ω^(o ⊕ 1)`, `K₂` and four `1`s, and `φ_a(b)` is closed under
all of them. -/

/-- **The climb to a notation below `φ_a(b)` stays below `φ_a(b)`, for `0 < a`.** -/
theorem height_lt_veblenNote {o a b : Gamma0Note} (ha : 0 < a)
    (ho : o < Gamma0Note.veblenNote a b) :
    gamma0Climb₂.height o < Gamma0Note.veblenNote a b := by
  have ha1 : (1 : Gamma0Note) ≤ a := Gamma0Note.one_le_of_pos ha
  have h1 : (1 : Gamma0Note) < Gamma0Note.veblenNote a b :=
    Gamma0Note.one_lt_veblenNote ha1
  have hK : K₂ < Gamma0Note.veblenNote a b := by
    rw [K₂_eq_ofNat]
    exact Gamma0Note.ofNat_lt_veblenNote c₂ ha1
  have hw : Gamma0Note.omegaPow (Gamma0Note.nadd o 1) < Gamma0Note.veblenNote a b :=
    Gamma0Note.omegaPow_lt_veblenNote ha1 (Gamma0Note.nadd_lt_veblenNote ho h1)
  show Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.nadd (Gamma0Note.nadd
      (Gamma0Note.nadd (Gamma0Note.omegaPow (Gamma0Note.nadd o 1)) K₂) 1) 1) 1) 1
    < Gamma0Note.veblenNote a b
  exact Gamma0Note.nadd_lt_veblenNote (Gamma0Note.nadd_lt_veblenNote
    (Gamma0Note.nadd_lt_veblenNote (Gamma0Note.nadd_lt_veblenNote
      (Gamma0Note.nadd_lt_veblenNote hw hK) h1) h1) h1) h1

/-- The `a = 1` case: the climb to a notation below `ε_b` stays below `ε_b`. -/
theorem height_lt_epsilonNote {o b : Gamma0Note} (ho : o < Gamma0Note.epsilonNote b) :
    gamma0Climb₂.height o < Gamma0Note.epsilonNote b :=
  height_lt_veblenNote Gamma0Note.zero_lt_one ho

/-! ### The new axiom: `TIupto(≺₁, ā)` is derivable below `Γ₀`

The ω-rule over the instances of `∀ x ≺₁ ā, x ∈ X`.  For `k ≺₁ ā` the number `k`
codes a notation `o < a` and the climb gives `∼Prog, k̄ ∈ X` at `height o`, which
`height_lt` bounds by `ω^(a ⊕ 1)`; for the rest, `∼(k̄ ≺₁ ā)` is derivable at
`K₂`.  So the ω-rule runs at `ω^(a ⊕ 1)` and one `or` rule forms the axiom. -/

/-- **The ω-premises.** -/
theorem premise (a : Gamma0Note) (k : ℕ) :
    ∃ β : Gamma0Note, β < Gamma0Note.omegaPow (Gamma0Note.nadd a 1) ∧
      D₂ β (evInst₂.inst (ev₂ (belowBody₂ gamma0Order₂ (gamma0Code a))) k
        :: [ev₂ (∼(Prog₂ gamma0Order₂.prec))]) := by
  rw [inst_belowBody₂, ev₂_precOrXat₂_eq]
  by_cases hk : precN₁ k (gamma0Code a)
  · obtain ⟨o, rfl⟩ := (precN₁_dom hk).1
    have ho : o < a := lt_of_precN₁_code hk
    refine ⟨OrdinalNotation.succ (gamma0Climb₂.height o), ?_, ?_⟩
    · exact OrdinalNotation.nadd_lt_omegaPow (gamma0Climb₂.height_lt ho) (one_lt₂ a)
    · refine OmegaDerivable₂.or (OrdinalNotation.lt_succ _) ?_
      refine OmegaDerivable₂.contraction ?_ (gamma0_climb_code o)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr (Or.inr rfl)
      · exact Or.inr (Or.inl rfl)
  · refine ⟨OrdinalNotation.succ K₂, ?_, ?_⟩
    · exact OrdinalNotation.nadd_lt_omegaPow (K₂_lt a) (one_lt₂ a)
    · refine OmegaDerivable₂.or (OrdinalNotation.lt_succ _) ?_
      refine OmegaDerivable₂.contraction ?_ (neg_precAt₂_gamma0 hk)
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      rcases hx with rfl
      exact Or.inl rfl

/-- The evaluated axiom, in the shape the rules produce. -/
theorem ev₂_TIupto₂_gamma0 (a : Gamma0Note) :
    ev₂ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)))
      = ev₂ (∼(Prog₂ gamma0Order₂.prec))
        ⋎ (∀¹ (ev₂ (belowBody₂ gamma0Order₂ (gamma0Code a)))) := by
  rw [TIupto₂_numAt, ev₂_or, ev₂_belowAt₂_eq]

/-- **`TIupto(≺₁, ā)` is derivable at height `ω^(a ⊕ 1) + 1`.** -/
theorem TIupto₂_derivable_at (a : Gamma0Note) :
    D₂ (OrdinalNotation.succ (Gamma0Note.omegaPow (Gamma0Note.nadd a 1)))
      [ev₂ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)))] := by
  rw [ev₂_TIupto₂_gamma0]
  refine OmegaDerivable₂.or (OrdinalNotation.lt_succ _) ?_
  choose β hβ using premise a
  have h : D₂ (Gamma0Note.omegaPow (Gamma0Note.nadd a 1))
      [∀¹ (ev₂ (belowBody₂ gamma0Order₂ (gamma0Code a))),
        ev₂ (∼(Prog₂ gamma0Order₂.prec))] :=
    OmegaDerivable₂.omegaRule β (fun k => (hβ k).1) (fun k => (hβ k).2)
  refine OmegaDerivable₂.contraction ?_ h
  intro x hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
  rcases hx with rfl | rfl
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- **The new axiom is cut-free derivable below `ε_b`, for every `b` above `a`.**
Every `ε_b` is below `Γ₀`, so this is the `Γ₀` station's height bound; taking
`b := a ⊕ 1` gives the uniform form below. -/
theorem TIupto₂_derivable_lt (a b : Gamma0Note) (hab : a < b) :
    ∃ β : Gamma0Note, β < Gamma0Note.epsilonNote b ∧
      D₂ β [ev₂ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)))] := by
  have h1 : (1 : Gamma0Note) < Gamma0Note.epsilonNote b := Gamma0Note.one_lt_epsilon b
  have ha : a < Gamma0Note.epsilonNote b :=
    lt_of_lt_of_le hab (Gamma0Note.le_epsilon_self b)
  have hn : Gamma0Note.nadd a 1 < Gamma0Note.epsilonNote b :=
    Gamma0Note.nadd_lt_epsilon ha h1
  have hw : Gamma0Note.omegaPow (Gamma0Note.nadd a 1) < Gamma0Note.epsilonNote b :=
    Gamma0Note.omegaPow_lt_epsilon hn
  exact ⟨_, Gamma0Note.nadd_lt_epsilon hw h1, TIupto₂_derivable_at a⟩

/-- **`TIupto(≺₁, ā)` is cut-free derivable below `ε_{a ⊕ 1} = φ_1(a ⊕ 1) < Γ₀`.** -/
theorem TIupto₂_derivable (a : Gamma0Note) :
    ∃ β : Gamma0Note, β < Gamma0Note.veblenNote 1 (Gamma0Note.nadd a 1) ∧
      D₂ β [ev₂ (TIupto₂ gamma0Order₂.prec (numAt (gamma0Code a)))] :=
  TIupto₂_derivable_lt a (Gamma0Note.nadd a 1) (Gamma0Note.lt_nadd_one a)

/-- **The `ψ`-instance of the new axiom**, for every arithmetical unary `ψ`, at
the *same* height: `SubstX₂.lean`'s transport costs nothing. -/
theorem TIuptoψ₂_derivable (a : Gamma0Note) {ψ : Semiformula ℒₒᵣ ℕ ℕ 0 1} (hψ : Arith ψ) :
    ∃ β : Gamma0Note, β < Gamma0Note.veblenNote 1 (Gamma0Note.nadd a 1) ∧
      D₂ β [ev₂ (TIuptoψ₂ gamma0Order₂.prec ψ (numAt (gamma0Code a)))] := by
  obtain ⟨β, hβ, hd⟩ := TIupto₂_derivable a
  refine ⟨β, hβ, ?_⟩
  have h := OmegaDerivable₂.substX₂ (O := Gamma0Note) hψ hd
  simp only [List.map_cons, List.map_nil] at h
  rwa [substX₂_ev₂_TIupto₂ gamma0Order₂.setFree_prec] at h

end OrdinalAnalysis.ACAOmega.Climb₂
