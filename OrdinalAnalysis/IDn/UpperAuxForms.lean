/-
  The well-ordering operator forms of `ID_n`, for the internal
  order given by the formulas of an `OrderFormulas`, and their meaning in arithmetically standard
  structures.

  Write `fld(x)` for "`x` is a normal domain code", `x ≺ y` for the internal order, `Ω_{k+1}`
  for the code `tcOmega k` (`ThetaWTerm.Omega k`), and `I_j` for the predicate of level `j`
  (the symbol `I_(ix j)` of `LXIN ι`, for an index map `ix : ℕ → ι`).  The forms are

      A_0(Y, x)     :≡ ∀y (fld y ∧ fld x ∧ y ≺ x → Y y)                   (`wForm 0`)
      D_k(x)        :≡ fld x ∧ ⋀_{j<k} ∀δ (δ ∈ E_j(x) → I_j δ)             (`DF k`)
      A_{k+1}(Y, x) :≡ D_{k+1}(x) ∧ x ≺ Ω_{k+2} ∧ ∀y (D_{k+1}(y) ∧ y ≺ x → Y y)   (`wForm (k+1)`)

  so `I_0` is the accessible part of `≺` on the field, and `I_{k+1}` is the accessible part of
  `≺` restricted to the distinguished class `D_{k+1}` (the design's `D_k`: all coefficients of
  levels `≤ k` in the lower predicates), below `Ω_{k+2}`.  `WForms n` is the family of the
  first `n` forms on `LXIn n` (`ix j = j mod n`), `WFormsOmega` the family on `LXIomega`
  (`ix = id`).

  `eval_DF`, `eval_wForm_zero`, `eval_wForm_succ`: the forms in any `LXIN ι`-structure whose
  arithmetic reduct is standard, with the predicates `I_j` read as that structure reads them.
-/
import OrdinalAnalysis.IDn.UpperAux
import OrdinalAnalysis.IDn.Lift

set_option autoImplicit false

namespace OrdinalAnalysis.IDn.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDn.Internal

namespace OrderFormulas

variable (F : OrderFormulas)

/-- `fld(x)`: a normal domain code. -/
def fldWDef : 𝚺₁.Semisentence 1 := .mkSigma “x. !F.nfDef x ∧ !F.domDef x”

/-- `fld(y) ∧ fld(x) ∧ y ≺ x` (slot `0` the smaller element). -/
def precWDef : 𝚺₁.Semisentence 2 :=
  .mkSigma “y x. !F.nfDef y ∧ !F.domDef y ∧ !F.nfDef x ∧ !F.domDef x ∧ !F.ltDef y x”

/-- **The order of the upper bound**: `y ≺ x` on the field (normal domain codes). -/
def precW : Semisentence ℒₒᵣ 2 := F.precWDef.val

section Eval

variable {V : Type} [ORingStructure V]

@[simp] theorem eval_fldWDef (x : V) : F.fldWDef.val.Evalb ![x] ↔ F.fld x := by
  simp [fldWDef, fld]

@[simp] theorem eval_precWDef (y x : V) :
    F.precWDef.val.Evalb ![y, x] ↔ F.fld y ∧ F.fld x ∧ F.lt y x := by
  simp [precWDef, fld]
  tauto

end Eval

end OrderFormulas

/-! ### The forms -/

section Forms

variable (F : OrderFormulas) {ι : Type} (ix : ℕ → ι)

/-- An arithmetic formula in `LXIN ι`. -/
abbrev lm {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) : Semiformula (LXIN ι) ξ m :=
  Semiformula.lMap (toLXIN ι) φ

/-- `δ ∈ E_j(x)` for the standard level `j`, with `δ = #0`, `x = #1`. -/
def inEAt (j : ℕ) : Semisentence ℒₒᵣ 2 :=
  thInEDef.val ⇜ ![((j : ℕ) : Semiterm ℒₒᵣ Empty 2), #0, #1]

/-- `x ≺ Ω_{k+1}` (the code of `ThetaWTerm.Omega k`), with `x = #0`. -/
def ltOmegaAt (k : ℕ) : Semisentence ℒₒᵣ 1 :=
  F.ltDef.val ⇜ ![#0, ((code (ThetaWTerm.Omega k) : ℕ) : Semiterm ℒₒᵣ Empty 1)]

/-- **The distinguished classes** `D_k(x) :≡ fld x ∧ ⋀_{j<k} ∀δ (δ ∈ E_j(x) → I_j δ)`. -/
def DF : ℕ → Semisentence (LXIN ι) 1
  | 0 => lm F.fldWDef.val
  | k + 1 => DF k ⋏ (∀¹ (lm (inEAt k) 🡒 Iat (ix k) #0))

/-- **The well-ordering operator forms.** -/
def wForm : ℕ → Semisentence (LXIN ι) 1
  | 0 => ∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (ix 0) #0)
  | k + 1 => DF F ix (k + 1) ⋏ (lm (ltOmegaAt F (k + 1)) ⋏
      (∀¹ ((DF F ix (k + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (ix (k + 1)) #0)))

/-- The level map of `Fin n`: `j ↦ j mod n`. -/
def ixFin {n : ℕ} (h : 0 < n) (j : ℕ) : Fin n := ⟨j % n, Nat.mod_lt j h⟩

/-- **The forms of `ID_n`** (levels `0, …, n-1`). -/
def WForms (n : ℕ) : Fin n → Semisentence (LXIn n) 1 :=
  fun k => wForm F (ixFin (Fin.pos k)) k.val

/-- **The forms of `ID_{<ω}`** (all levels). -/
def WFormsOmega : ℕ → Semisentence LXIomega 1 := fun k => wForm F id k

end Forms

/-! ### The forms in an arithmetically standard structure -/

section EvalForms

variable (F : OrderFormulas) {ι : Type} (ix : ℕ → ι)
variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (S : Structure (LXIN ι) N) (hS : S.lMap (toLXIN ι) = Arithmetic.standardModel N)

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
include hS in
theorem eval_lm {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) (e : Fin m → N) (f : ξ → N) :
    Semiformula.Eval (s := S) e f (lm φ) ↔ Semiformula.Eval (s := standardModel N) e f φ := by
  rw [lm, Semiformula.eval_lMap, hS]

/-- `I_j` as read by `S`. -/
def relI (j : ι) (x : N) : Prop := S.rel (Sum.inr (IXRelN.I j)) ![x]

omit [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
theorem eval_Iat_S {ξ : Type*} {m : ℕ} (j : ι) (t : Semiterm (LXIN ι) ξ m) (e : Fin m → N)
    (f : ξ → N) :
    Semiformula.Eval (s := S) e f (Iat j t) ↔ relI S j (Semiterm.val (s := S) e f t) := by
  have h : (Semiterm.val (s := S) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := S) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg (S.rel (Sum.inr (IXRelN.I j))) h)

theorem eval_inEAt (j : ℕ) (δ x : N) :
    Semiformula.Evalb (M := N) ![δ, x] (inEAt j) ↔ iinE (j : N) δ x = 1 := by
  unfold inEAt
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := N) ![δ, x] Empty.elim ∘
      ![((j : ℕ) : Semiterm ℒₒᵣ Empty 2), #0, #1]) = ![(j : N), δ, x] := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [numeral_eq_natCast]
    · refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · refine Fin.cases ?_ (fun i => i.elim0) i
        simp
  rw [e, eval_thInEDef]

theorem eval_ltOmegaAt (k : ℕ) (x : N) :
    Semiformula.Evalb (M := N) ![x] (ltOmegaAt F k) ↔ F.lt x (tcOmega (k : N)) := by
  unfold ltOmegaAt
  rw [Semiformula.eval_substs]
  have e : (Semiterm.val (M := N) ![x] Empty.elim ∘
      ![(#0 : Semiterm ℒₒᵣ Empty 1), ((code (ThetaWTerm.Omega k) : ℕ) : Semiterm ℒₒᵣ Empty 1)])
        = ![x, tcOmega (k : N)] := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · refine Fin.cases ?_ (fun i => i.elim0) i
      rw [← mc_Omega]
      simp [mc, numeral_eq_natCast]
  rw [e]
  rfl

/-- `D_k` in `S`, recursively: `D_0 = fld`, `D_{k+1}(x) = D_k(x) ∧ E_k(x) ⊆ I_k`. -/
def DcS : ℕ → N → Prop
  | 0, x => F.fld x
  | k + 1, x => DcS k x ∧ ∀ δ, iinE (k : N) δ x = 1 → relI S (ix k) δ

include hS in
theorem eval_DF (k : ℕ) (x : N) :
    Semiformula.Eval (s := S) ![x] Empty.elim (DF F ix k) ↔ DcS F ix S k x := by
  induction k with
  | zero =>
    show Semiformula.Eval (s := S) ![x] Empty.elim (lm F.fldWDef.val) ↔ F.fld x
    rw [eval_lm S hS]
    exact OrderFormulas.eval_fldWDef F x
  | succ k ih =>
    show Semiformula.Eval (s := S) ![x] Empty.elim
        (DF F ix k ⋏ (∀¹ (lm (inEAt k) 🡒 Iat (ix k) #0))) ↔ _
    rw [LogicalConnective.HomClass.map_and, ih, Semiformula.eval_all]
    refine and_congr Iff.rfl (forall_congr' fun δ => ?_)
    rw [LogicalConnective.HomClass.map_imply, eval_lm S hS, eval_Iat_S]
    have e : (δ :> ![x] : Fin 2 → N) = ![δ, x] := by
      funext i; refine Fin.cases rfl (fun j => ?_) i; rfl
    rw [e, eval_inEAt]
    rfl

omit [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] in
include hS in
theorem eval_wForm_zero (x : N) :
    Semiformula.Eval (s := S) ![x] Empty.elim (wForm F ix 0) ↔
      ∀ y, F.fld y → F.fld x → F.lt y x → relI S (ix 0) y := by
  show Semiformula.Eval (s := S) ![x] Empty.elim (∀¹ (lm (OrderFormulas.precW F) 🡒 Iat (ix 0) #0)) ↔ _
  rw [Semiformula.eval_all]
  refine forall_congr' fun y => ?_
  rw [LogicalConnective.HomClass.map_imply, eval_lm S hS, eval_Iat_S]
  have e : (y :> ![x] : Fin 2 → N) = ![y, x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; rfl
  rw [e]
  show (F.precWDef.val.Evalb ![y, x] → _) ↔ _
  rw [OrderFormulas.eval_precWDef]
  constructor
  · intro h hy hx hlt; exact h ⟨hy, hx, hlt⟩
  · rintro h ⟨hy, hx, hlt⟩; exact h hy hx hlt

include hS in
theorem eval_wForm_succ (k : ℕ) (x : N) :
    Semiformula.Eval (s := S) ![x] Empty.elim (wForm F ix (k + 1)) ↔
      DcS F ix S (k + 1) x ∧ F.lt x (tcOmega ((k + 1 : ℕ) : N)) ∧
        ∀ y, DcS F ix S (k + 1) y → F.lt y x → relI S (ix (k + 1)) y := by
  show Semiformula.Eval (s := S) ![x] Empty.elim (DF F ix (k + 1) ⋏ (lm (ltOmegaAt F (k + 1)) ⋏
      (∀¹ ((DF F ix (k + 1) ⇜ ![#0]) ⋏ lm F.ltDef.val 🡒 Iat (ix (k + 1)) #0)))) ↔ _
  rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and, eval_DF F ix S hS,
    eval_lm S hS, eval_ltOmegaAt, Semiformula.eval_all]
  refine and_congr Iff.rfl (and_congr Iff.rfl (forall_congr' fun y => ?_))
  rw [LogicalConnective.HomClass.map_imply, LogicalConnective.HomClass.map_and,
    Semiformula.eval_substs, eval_lm S hS, eval_Iat_S]
  have e1 : (Semiterm.val (s := S) (y :> ![x]) Empty.elim ∘ ![(#0 : Semiterm (LXIN ι) Empty 2)])
      = ![y] := by
    funext i; refine Fin.cases rfl (fun j => j.elim0) i
  have e : (y :> ![x] : Fin 2 → N) = ![y, x] := by
    funext i; refine Fin.cases rfl (fun j => ?_) i; rfl
  rw [e1, eval_DF F ix S hS, e]
  show (DcS F ix S (k + 1) y ∧ F.ltDef.val.Evalb ![y, x] → _) ↔ _
  constructor
  · intro h hy hlt; exact h ⟨hy, hlt⟩
  · rintro h ⟨hy, hlt⟩; exact h hy hlt

end EvalForms

end OrdinalAnalysis.IDn.Upper
