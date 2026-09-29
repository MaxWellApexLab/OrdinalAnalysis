/-
  The uniform well-ordering operator form of `ID_ω` and its reading in any model.

  Sources: W. Buchholz and W. Pohlers, *Provable wellorderings of formal theories for
  transfinitely iterated inductive definitions*, J. Symbolic Logic 43 (1978), p. 121: the one
  form `𝔄[X, Y, x, y] :≡ 𝔤[x] ∧ ∀x₀ ≺ x (𝔤[x₀] → x₀ ∈ X)` with
  `𝔤[x] :≡ x ≺ Ω_y ∧ ∀z < y ({⟨z, x₁⟩ : x₁ ∈ K_z x} ⊆ Y)`, defining `W_u` as the accessible part
  of `M_u` for every level `u` at once (their (W1), (W2)).  The per-level forms of `ID_n` are
  `IDn/UpperAuxForms.lean` (`wForm k`, one form per level); here the level is an argument.

  Write `fld(x)` for "`x` is a normal domain code", `x ≺ y` for the internal order, `Ω_{y+1}` for
  the code `tcOmega y` (`ThetaVTerm.Omega y`), `E_j(x)` for the coefficient set `iinE j · x`.  With
  `#0 = x` (the object) and `#1 = y` (the level), and `P`, `Q` the schema predicates of `LForm`:

      D(y, x) :≡ fld x ∧ ∀j (j < y → ∀δ (δ ∈ E_j(x) → Q(j, δ)))                    (`DAt`)
      A(y, x) :≡ D(y, x) ∧ x ≺ Ω_{y+1} ∧ ∀z (D(y, z) ∧ z ≺ x → P z)                (`WFormW`)

  `WFormW ltD nfD domD` takes the three `Σ₁` formulas of the order (`x ≺ y`, `NF`, `Dom`) as
  arguments (the three fields of `IDn`'s `OrderFormulas`); `WFormWc` is the instance with the
  internal order of `IDw/Internal/Order.lean`.  `P` occurs once, positively (`positiveP_WFormW`);
  `Q` occurs in both polarities, which `IDw`'s `PositiveP` allows.

  **Reading.**  In `IDw A`, the level-`y` instance of `A` is `AAt F Y A`: `P(t) ↦ F(t, Y)`,
  `Q(s, t) ↦ s < Y ∧ J(s, t)`.  `eval_AAt`: in *any* `LXJ`-structure on `N` whose arithmetic
  reduct is the arithmetic of `N`, `AAt F Y φ` holds iff `φ` holds in the `LForm`-structure
  `formStr Pr Qr` with `P` read as `Pr t :≡ F(t, y)` and `Q` as `Qr a b :≡ a < y ∧ J(a, b)`
  (`y` the value of `Y`).  With `eval_WFormW` this gives, for the model's `J` (`Jm`):

  * `closure_of_eval`: `D_y(x) ∧ x ≺ Ω_{y+1} ∧ (∀z ∈ D_y, z ≺ x → J(y, z)) → J(y, x)`;
  * `ind_of_eval`, `ind_of_eval_definable`: for every predicate `P` definable in `LXJ` with
    parameters, `(∀x, D_y(x) ∧ x ≺ Ω_{y+1} ∧ (∀z ∈ D_y, z ≺ x → P z) → P x) → J(y, ·) ⊆ P`,

  where `D_y(x) :≡ fld x ∧ ∀ j < y, E_j(x) ⊆ J(j, ·)` (`DcR`).  That is: **`J(y, ·)` is the
  accessible part of `≺` restricted to `D_y` below `Ω_{y+1}`, `D_y` the codes whose coefficients
  of every level `j < y` lie in `J(j, ·)`** — BP78's `W_u` and `M_u`, for an internal level `y`.
-/
import OrdinalAnalysis.IDw.Theory
import OrdinalAnalysis.EvalWrap
import OrdinalAnalysis.IDw.Internal.Order
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option warn.classDefReducibility false

namespace OrdinalAnalysis.IDw.Upper

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.HierarchySymbol
open OrdinalAnalysis.IDw.Internal

/-! ### Arithmetic pieces -/

/-- The embedding of arithmetic into the schema language `LForm`. -/
abbrev toLForm : ℒₒᵣ →ᵥ LForm := Language.Hom.add₁ ℒₒᵣ PQLang

/-- An arithmetic formula as an `LForm`-formula. -/
abbrev lf {ξ : Type*} {m : ℕ} (φ : Semiformula ℒₒᵣ ξ m) : Semiformula LForm ξ m :=
  Semiformula.lMap toLForm φ

section Pieces

variable (ltD : 𝚺₁.Semisentence 2) (nfD domD : 𝚺₁.Semisentence 1)

/-- `fld(x)`: `NF x ∧ Dom x`. -/
def fldDefW : 𝚺₁.Semisentence 1 := .mkSigma “x. !nfD x ∧ !domD x”

/-- `x ≺ Ω_{y+1}` (slot `0` is `x`, slot `1` the level `y`). -/
def ltOmegaDefW : 𝚺₁.Semisentence 2 := .mkSigma “x y. ∃ o, !tcOmegaDef o y ∧ !ltD x o”

end Pieces

/-- `x < y` on the numbers. -/
def ltNatDef : Semisentence ℒₒᵣ 2 := “x y. x < y”

/-! ### The form -/

section Forms

variable (ltD : 𝚺₁.Semisentence 2) (nfD domD : 𝚺₁.Semisentence 1)

/-- **The distinguished class** `D(y, x) :≡ fld x ∧ ∀j < y ∀δ (δ ∈ E_j(x) → Q(j, δ))`, at
arithmetic terms `x`, `y`. -/
def DAt {n : ℕ} (x y : Semiterm ℒₒᵣ Empty n) : Semiformula LForm Empty n :=
  lf ((fldDefW nfD domD).val ⇜ ![x]) ⋏
    (∀¹ (lf (ltNatDef ⇜ ![#0, Rew.bShift y]) 🡒
      (∀¹ (lf (thInEDef.val ⇜ ![#1, #0, Rew.bShift (Rew.bShift x)]) 🡒 Qat #1 #0))))

/-- **The uniform well-ordering form** `A(y, x) :≡ D(y, x) ∧ x ≺ Ω_{y+1} ∧
∀z (D(y, z) ∧ z ≺ x → P z)` (`#0 = x`, `#1 = y`). -/
def WFormW : FormJ :=
  DAt nfD domD #0 #1 ⋏ (lf (ltOmegaDefW ltD).val ⋏
    (∀¹ ((DAt nfD domD #0 #2 ⋏ lf (ltD.val ⇜ ![#0, #1])) 🡒 Pat #0)))

end Forms

/-- `x ≺ y` for the internal order `iltb` of `IDw/Internal/Order.lean`. -/
def iltDefW : 𝚺₁.Semisentence 2 := .mkSigma “x y. !iltbDef 1 x y”

/-- **The form with the internal order of `IDw/Internal`.** -/
def WFormWc : FormJ := WFormW iltDefW thNFDef thDomDef

/-! ### Positivity -/

section Positivity

variable {ξ : Type*}

/-- `φ` does not mention `P` at all. -/
def NoP : {n : ℕ} → Semiformula LForm ξ n → Prop
  | _, .verum => True
  | _, .falsum => True
  | _, .rel (Sum.inl _) _ => True
  | _, .rel (Sum.inr PQRel.Q) _ => True
  | _, .rel (Sum.inr PQRel.P) _ => False
  | _, .nrel (Sum.inl _) _ => True
  | _, .nrel (Sum.inr PQRel.Q) _ => True
  | _, .nrel (Sum.inr PQRel.P) _ => False
  | _, .and φ ψ => NoP φ ∧ NoP ψ
  | _, .or φ ψ => NoP φ ∧ NoP ψ
  | _, .all φ => NoP φ
  | _, .exs φ => NoP φ

theorem positiveP_of_noP : ∀ {n : ℕ} {φ : Semiformula LForm ξ n}, NoP φ → PositiveP φ
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel _ _, _ => trivial
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr PQRel.Q) _, _ => trivial
  | _, .nrel (Sum.inr PQRel.P) _, h => h.elim
  | _, .and _ _, h => ⟨positiveP_of_noP h.1, positiveP_of_noP h.2⟩
  | _, .or _ _, h => ⟨positiveP_of_noP h.1, positiveP_of_noP h.2⟩
  | _, .all _, h => positiveP_of_noP (n := _ + 1) h
  | _, .exs _, h => positiveP_of_noP (n := _ + 1) h

theorem noP_neg : ∀ {n : ℕ} {φ : Semiformula LForm ξ n}, NoP φ → NoP (∼φ)
  | _, .verum, _ => trivial
  | _, .falsum, _ => trivial
  | _, .rel (Sum.inl _) _, _ => trivial
  | _, .rel (Sum.inr PQRel.Q) _, _ => trivial
  | _, .rel (Sum.inr PQRel.P) _, h => h.elim
  | _, .nrel (Sum.inl _) _, _ => trivial
  | _, .nrel (Sum.inr PQRel.Q) _, _ => trivial
  | _, .nrel (Sum.inr PQRel.P) _, h => h.elim
  | _, .and _ _, h => ⟨noP_neg h.1, noP_neg h.2⟩
  | _, .or _ _, h => ⟨noP_neg h.1, noP_neg h.2⟩
  | _, .all _, h => noP_neg (n := _ + 1) h
  | _, .exs _, h => noP_neg (n := _ + 1) h

theorem noP_lf : ∀ {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n), NoP (lf φ)
  | _, .verum => trivial
  | _, .falsum => trivial
  | _, .rel _ _ => trivial
  | _, .nrel _ _ => trivial
  | _, .and φ ψ => ⟨noP_lf φ, noP_lf ψ⟩
  | _, .or φ ψ => ⟨noP_lf φ, noP_lf ψ⟩
  | _, .all φ => noP_lf (n := _ + 1) φ
  | _, .exs φ => noP_lf (n := _ + 1) φ

theorem noP_DAt (nfD domD : 𝚺₁.Semisentence 1) {n : ℕ} (x y : Semiterm ℒₒᵣ Empty n) :
    NoP (DAt nfD domD x y) :=
  ⟨noP_lf _, noP_neg (noP_lf _), noP_neg (noP_lf _), trivial⟩

/-- **The form is positive in `P`.** -/
theorem positiveP_WFormW (ltD : 𝚺₁.Semisentence 2) (nfD domD : 𝚺₁.Semisentence 1) :
    PositiveP (WFormW ltD nfD domD) :=
  ⟨positiveP_of_noP (noP_DAt nfD domD _ _), positiveP_of_noP (noP_lf _),
    positiveP_of_noP (noP_neg ⟨noP_DAt nfD domD _ _, noP_lf _⟩), trivial⟩

theorem positiveP_WFormWc : PositiveP WFormWc := positiveP_WFormW _ _ _

end Positivity

/-! ### The schema language read on a structure -/

section Reading

variable {N : Type*} [ORingStructure N]

/-- The schema predicates on `N`: `P` read by `Pr`, `Q` by `Qr`. -/
def pqStruc (Pr : N → Prop) (Qr : N → N → Prop) : Structure PQLang N where
  func := fun _ fn _ => PEmpty.elim fn
  rel := fun _ r v => match r with
    | PQRel.P => Pr (v 0)
    | PQRel.Q => Qr (v 0) (v 1)

/-- The `LForm`-structure on `N`: arithmetic of `N`, `P` read by `Pr`, `Q` by `Qr`. -/
def formStr (Pr : N → Prop) (Qr : N → N → Prop) : Structure LForm N :=
  Structure.add ℒₒᵣ PQLang N (str₂ := pqStruc Pr Qr)

variable (Pr : N → Prop) (Qr : N → N → Prop)

@[simp] theorem eval_lf_formStr {ξ : Type*} {n : ℕ} (φ : Semiformula ℒₒᵣ ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := formStr Pr Qr) e f (lf φ) ↔ Semiformula.Eval (M := N) e f φ :=
  Structure.eval_lMap_add₁ (str₂ := pqStruc Pr Qr) φ e f

theorem eval_Pat_formStr {ξ : Type*} {n : ℕ} (t : Semiterm LForm ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := formStr Pr Qr) e f (Pat t) ↔
      Pr (Semiterm.val (s := formStr Pr Qr) e f t) := by
  have h : (Semiterm.val (s := formStr Pr Qr) e f ∘ ![t] : Fin 1 → N)
      = ![Semiterm.val (s := formStr Pr Qr) e f t] := Matrix.comp₁ t
  exact Iff.of_eq (congrArg ((formStr Pr Qr).rel (Sum.inr PQRel.P)) h)

theorem eval_Qat_formStr {ξ : Type*} {n : ℕ} (a b : Semiterm LForm ξ n) (e : Fin n → N)
    (f : ξ → N) :
    Semiformula.Eval (s := formStr Pr Qr) e f (Qat a b) ↔
      Qr (Semiterm.val (s := formStr Pr Qr) e f a) (Semiterm.val (s := formStr Pr Qr) e f b) := by
  have h : (Semiterm.val (s := formStr Pr Qr) e f ∘ ![a, b] : Fin 2 → N)
      = ![Semiterm.val (s := formStr Pr Qr) e f a, Semiterm.val (s := formStr Pr Qr) e f b] :=
    Matrix.comp₂ a b
  exact Iff.of_eq (congrArg ((formStr Pr Qr).rel (Sum.inr PQRel.Q)) h)

variable [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (ltD : 𝚺₁.Semisentence 2) (nfD domD : 𝚺₁.Semisentence 1)

/-- `fld(x)` for the formulas `nfD`, `domD`. -/
def FldR (x : N) : Prop := nfD.val.Evalb ![x] ∧ domD.val.Evalb ![x]

/-- `x ≺ y` for the formula `ltD`. -/
def LtR (x y : N) : Prop := ltD.val.Evalb ![x, y]

/-- **The distinguished class of level `y`**, relative to a reading `Qr` of the lower levels. -/
def DcR (y x : N) : Prop := FldR nfD domD x ∧ ∀ j < y, ∀ δ, iinE j δ x = 1 → Qr j δ

/-- **The form read in `N`**: `D_y(x) ∧ x ≺ Ω_{y+1} ∧ ∀z ∈ D_y, z ≺ x → Pr z`. -/
def AccR (y x : N) : Prop :=
  DcR Qr nfD domD y x ∧ LtR ltD x (tcOmega y) ∧
    ∀ z, DcR Qr nfD domD y z → LtR ltD z x → Pr z

theorem eval_DAt (x y : N) :
    Semiformula.Eval (s := formStr Pr Qr) ![x, y] Empty.elim
        (DAt nfD domD (#0 : Semiterm ℒₒᵣ Empty 2) #1) ↔ DcR Qr nfD domD y x := by
  have e1 : (fun _ : Fin 1 => x) = ![x] := by funext i; fin_cases i; rfl
  simp only [DAt, DcR, FldR, fldDefW, ltNatDef, eval_Qat_formStr, Function.comp_def,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_all, eval_lf_formStr, Semiformula.eval_substs]
  simp [e1]
  intro _ _
  refine forall_congr' fun j => imp_congr_right fun _ => forall_congr' fun δ => imp_congr_left ?_
  have e2 : (fun i => Semiterm.val (M := N) ![δ, j, x, y] Empty.elim
      (![(#1 : Semiterm ℒₒᵣ Empty 4), #0, #2] i)) = ![j, δ, x] := by
    funext i; fin_cases i <;> rfl
  rw [e2]; exact eval_thInEDef j δ x

theorem eval_DAt' (z x y : N) :
    Semiformula.Eval (s := formStr Pr Qr) ![z, x, y] Empty.elim
        (DAt nfD domD (#0 : Semiterm ℒₒᵣ Empty 3) #2) ↔ DcR Qr nfD domD y z := by
  have e1 : (fun _ : Fin 1 => z) = ![z] := by funext i; fin_cases i; rfl
  simp only [DAt, DcR, FldR, fldDefW, ltNatDef, eval_Qat_formStr, Function.comp_def,
    LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_imply,
    Semiformula.eval_all, eval_lf_formStr, Semiformula.eval_substs]
  simp [e1]
  intro _ _
  refine forall_congr' fun j => imp_congr_right fun _ => forall_congr' fun δ => imp_congr_left ?_
  have e2 : (fun i => Semiterm.val (M := N) ![δ, j, z, x, y] Empty.elim
      (![(#1 : Semiterm ℒₒᵣ Empty 5), #0, #2] i)) = ![j, δ, z] := by
    funext i; fin_cases i <;> rfl
  rw [e2]; exact eval_thInEDef j δ z

/-- **The form, read.** -/
theorem eval_WFormW (x y : N) :
    Semiformula.Eval (s := formStr Pr Qr) ![x, y] Empty.elim (WFormW ltD nfD domD) ↔
      AccR Pr Qr ltD nfD domD y x := by
  simp only [WFormW, LogicalConnective.HomClass.map_and, Semiformula.eval_all,
    LogicalConnective.HomClass.map_imply, eval_DAt, eval_DAt', AccR, eval_lf_formStr,
    eval_Pat_formStr, LogicalConnective.Prop.and_eq, LogicalConnective.Prop.arrow_eq]
  refine and_congr Iff.rfl (and_congr ?_ (forall_congr' fun z => ?_))
  · simp [ltOmegaDefW, LtR, tcOmega_defined.iff]
  · simp [LtR]

end Reading

/-! ### `AAt` in any structure with standard arithmetic -/

section AAt

variable {N : Type*} [ORingStructure N] [s : Structure LXJ N]

/-- `J(k, x)` as read by the structure. -/
def Jm (k x : N) : Prop := s.rel (Sum.inr XJRel.J) ![k, x]

omit [ORingStructure N] in
theorem eval_Jat_Jm {ξ : Type*} {n : ℕ} (a b : Semiterm LXJ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (Jat a b) ↔
      Jm (Semiterm.val (s := s) e f a) (Semiterm.val (s := s) e f b) := by
  have h : (Semiterm.val (s := s) e f ∘ ![a, b] : Fin 2 → N)
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := Matrix.comp₂ a b
  exact Iff.of_eq (congrArg (s.rel (Sum.inr XJRel.J)) h)

variable (hS : s.lMap toLXJ = Arithmetic.standardModel N)
include hS

theorem func_inl_eq {k : ℕ} (fn : (ℒₒᵣ).Func k) (w : Fin k → N) :
    s.func (Sum.inl fn) w = (Arithmetic.standardModel N).func fn w :=
  congrArg (fun S : Structure ℒₒᵣ N => S.func fn w) hS

theorem rel_inl_iff {k : ℕ} (r : (ℒₒᵣ).Rel k) (w : Fin k → N) :
    s.rel (Sum.inl r) w ↔ (Arithmetic.standardModel N).rel r w :=
  Iff.of_eq (congrArg (fun S : Structure ℒₒᵣ N => S.rel r w) hS)

theorem eval_ltAt_lt {ξ : Type*} {n : ℕ} (a b : Semiterm LXJ ξ n) (e : Fin n → N) (f : ξ → N) :
    Semiformula.Eval (s := s) e f (ltAt a b) ↔
      Semiterm.val (s := s) e f a < Semiterm.val (s := s) e f b := by
  have h : (fun i => Semiterm.val (s := s) e f (![a, b] i))
      = ![Semiterm.val (s := s) e f a, Semiterm.val (s := s) e f b] := Matrix.comp₂ a b
  show s.rel (Sum.inl Language.LT.lt) (fun i => Semiterm.val (s := s) e f (![a, b] i)) ↔ _
  rw [h, rel_inl_iff hS]
  exact Structure.lt_lang

variable (Pr : N → Prop) (Qr : N → N → Prop)

/-- An `LForm`-term cast into `LXJ` has the same value. -/
theorem val_termCast {ξ : Type*} {n : ℕ} (e : Fin n → N) (f : ξ → N) (t : Semiterm LForm ξ n) :
    Semiterm.val (s := s) e f (termCast t) = Semiterm.val (s := formStr Pr Qr) e f t := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func fn v ih =>
    rcases fn with fn | fn
    · show s.func (Sum.inl fn) (fun i => Semiterm.val (s := s) e f (termCast (v i))) =
        (Arithmetic.standardModel N).func fn (fun i => Semiterm.val (s := formStr Pr Qr) e f (v i))
      rw [func_inl_eq hS]
      exact congrArg _ (funext ih)
    · exact PEmpty.elim fn

/-- **`AAt` read in any structure with standard arithmetic**: `A_y(F, ·)` is `A` with `P` read
as `F(·, y)` and `Q` as `(a, b) ↦ a < y ∧ J(a, b)`. -/
theorem eval_AAt {ξ : Type*} (F : Semiformula LXJ ξ 2) (f : ξ → N) (y : N) {n : ℕ}
    (φ : Semiformula LForm ξ n) (Y : Semiterm LXJ ξ n) (e : Fin n → N)
    (hY : Semiterm.val (s := s) e f Y = y) :
    Semiformula.Eval (s := s) e f (AAt F Y φ) ↔
      Semiformula.Eval (s := formStr (fun t => Semiformula.Eval (s := s) ![t, y] f F)
        (fun a b => a < y ∧ Jm a b)) e f φ := by
  set Pr : N → Prop := fun t => Semiformula.Eval (s := s) ![t, y] f F
  set Qr : N → N → Prop := fun a b => a < y ∧ Jm a b
  induction φ using Semiformula.rec' with
  | hverum => simp [AAt]
  | hfalsum => simp [AAt]
  | hrel r v =>
    rcases r with r | r
    · show s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (termCast (v i))) ↔
        (Arithmetic.standardModel N).rel r (fun i => Semiterm.val (s := formStr Pr Qr) e f (v i))
      rw [rel_inl_iff hS]
      exact Iff.of_eq (congrArg _ (funext fun i => val_termCast hS Pr Qr e f (v i)))
    · cases r with
      | P =>
        show Semiformula.Eval (s := s) e f (F/[termCast (v 0), Y]) ↔ Pr _
        rw [Semiformula.eval_substs]
        have hc : (Semiterm.val (s := s) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := formStr Pr Qr) e f (v 0), y] := by
          rw [Matrix.comp₂, val_termCast hS Pr Qr, hY]
        rw [hc]
      | Q =>
        show Semiformula.Eval (s := s) e f
            (ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1))) ↔ Qr _ _
        rw [LogicalConnective.HomClass.map_and, eval_ltAt_lt hS, eval_Jat_Jm,
          val_termCast hS Pr Qr, val_termCast hS Pr Qr, hY]
        exact Iff.rfl
  | hnrel r v =>
    rcases r with r | r
    · show ¬ s.rel (Sum.inl r) (fun i => Semiterm.val (s := s) e f (termCast (v i))) ↔
        ¬ (Arithmetic.standardModel N).rel r (fun i => Semiterm.val (s := formStr Pr Qr) e f (v i))
      rw [rel_inl_iff hS]
      exact Iff.of_eq (congrArg _ (congrArg _ (funext fun i => val_termCast hS Pr Qr e f (v i))))
    · cases r with
      | P =>
        show Semiformula.Eval (s := s) e f (∼(F/[termCast (v 0), Y])) ↔ ¬ Pr _
        rw [LogicalConnective.HomClass.map_neg, Semiformula.eval_substs]
        have hc : (Semiterm.val (s := s) e f ∘ ![termCast (v 0), Y] : Fin 2 → N)
            = ![Semiterm.val (s := formStr Pr Qr) e f (v 0), y] := by
          rw [Matrix.comp₂, val_termCast hS Pr Qr, hY]
        rw [hc]
        exact Iff.rfl
      | Q =>
        show Semiformula.Eval (s := s) e f
            (∼(ltAt (termCast (v 0)) Y ⋏ Jat (termCast (v 0)) (termCast (v 1)))) ↔ ¬ Qr _ _
        rw [LogicalConnective.HomClass.map_neg, LogicalConnective.HomClass.map_and,
          eval_ltAt_lt hS, eval_Jat_Jm, val_termCast hS Pr Qr, val_termCast hS Pr Qr, hY]
        exact Iff.rfl
  | hand φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (AAt F Y φ ⋏ AAt F Y ψ) ↔ _
    rw [LogicalConnective.HomClass.map_and, LogicalConnective.HomClass.map_and]
    exact and_congr (ihφ Y e hY) (ihψ Y e hY)
  | hor φ ψ ihφ ihψ =>
    show Semiformula.Eval (s := s) e f (AAt F Y φ ⋎ AAt F Y ψ) ↔ _
    rw [LogicalConnective.HomClass.map_or, LogicalConnective.HomClass.map_or]
    exact or_congr (ihφ Y e hY) (ihψ Y e hY)
  | hall φ ih =>
    show Semiformula.Eval (s := s) e f (∀¹ AAt F (Rew.bShift Y) φ) ↔ _
    rw [Semiformula.eval_all, Semiformula.eval_all]
    exact forall_congr' fun x => ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hY)
  | hexs φ ih =>
    show Semiformula.Eval (s := s) e f (∃¹ AAt F (Rew.bShift Y) φ) ↔ _
    rw [Semiformula.eval_ex, Semiformula.eval_ex]
    exact exists_congr fun x => ih (Rew.bShift Y) (x :> e) (by rw [Semiterm.val_bShift]; exact hY)

end AAt

/-! ### The two axioms, read -/

section Axioms

variable {N : Type} [ORingStructure N] [s : Structure LXJ N]
variable (hS : s.lMap toLXJ = Arithmetic.standardModel N)

/-- The lower levels below `y`, as the closure axiom reads `Q`. -/
def lowJ (y a b : N) : Prop := a < y ∧ Jm a b

/- The axioms are read for any form `A` whose reading in `formStr Pr Qr` at `(x, y)` is
`R Pr Qr y x`; `eval_WFormW` supplies this for `WFormW`. -/
variable (A : FormJ) (R : (N → Prop) → (N → N → Prop) → N → N → Prop)
  (hA : ∀ (Pr : N → Prop) (Qr : N → N → Prop) (x y : N),
    Semiformula.Eval (s := formStr Pr Qr) ![x, y] Empty.elim A ↔ R Pr Qr y x)

include hS hA in
/-- **Closure**, read: `R (J(y, ·)) J^{<y} y x → J(y, x)`. -/
theorem closure_of_eval
    (h : Semiformula.Eval (s := s) ![] Empty.elim (closureAxJ A))
    (y x : N) (hx : R (Jm y) (lowJ y) y x) : Jm y x := by
  rw [closureAxJ, Semiformula.eval_all] at h
  have h := h y
  rw [Semiformula.eval_all] at h
  have h := h x
  rw [LogicalConnective.HomClass.map_imply] at h
  have e : (x :> y :> ![] : Fin 2 → N) = ![x, y] := rfl
  rw [e, eval_Jat_Jm] at h
  refine h ?_
  rw [eval_AAt hS (Jat #1 #0) Empty.elim y A #1 ![x, y] rfl, hA]
  have hP : (fun t => Semiformula.Eval (s := s) ![t, y] Empty.elim
      (Jat (#1 : Semiterm LXJ Empty 2) #0)) = Jm y := funext fun t => by rw [eval_Jat_Jm]; rfl
  rw [hP]
  exact hx

include hS hA in
/-- **Induction**, read, for the formula `F` under the assignment `f`. -/
theorem ind_of_eval (F : Semiformula LXJ ℕ 2)
    (h : Semiformula.Eval (s := s) ![] Empty.elim (indAxJ A F)) (f : ℕ → N) (y : N)
    (hprog : ∀ x, R (fun t => Semiformula.Eval (s := s) ![t, y] f F) (lowJ y) y x →
      Semiformula.Eval (s := s) ![x, y] f F) :
    ∀ x, Jm y x → Semiformula.Eval (s := s) ![x, y] f F := by
  have : Nonempty N := ⟨0⟩
  rw [indAxJ] at h
  have h := (Semiformula.eval_univCl (s := s) _).mp h f
  simp only [Semiformula.Evalf, LogicalConnective.HomClass.map_imply, Semiformula.eval_all] at h
  intro x hx
  have e : ∀ t : N, (t :> ![y] : Fin 2 → N) = ![t, y] := fun t => rfl
  refine h y (fun z hz => ?_) x ?_
  · rw [e] at hz ⊢
    refine hprog z ?_
    rw [eval_AAt hS F f y (Rewriting.emb A) #1 ![z, y] rfl, Semiformula.eval_emb, hA] at hz
    exact hz
  · rw [e, eval_Jat_Jm]
    exact hx

omit [ORingStructure N] in
/-- A predicate definable with parameters is defined by a formula with free variables numbered
by `ℕ`, under a suitable assignment (the proof of `IDn.Lift.exists_nat_formula_pred`). -/
theorem natFormula_of_definable [Inhabited N] {P : N → Prop} (hP : LXJ.DefinablePred P) :
    ∃ (ψ : Semiformula LXJ ℕ 1) (f : ℕ → N),
      ∀ x, Semiformula.Eval (s := s) ![x] f ψ ↔ P x := by
  classical
  obtain ⟨φ, hφ⟩ := hP.definable
  refine ⟨Rew.rewriteMap φ.idxOfFVar ▹ φ, φ.enumerateFVar, fun x => ?_⟩
  rw [Semiformula.eval_rewriteMap]
  exact (Semiformula.eval_enumerateFVar_idxOfFVar_eq_id φ ![x]).trans (hφ ![x])

include hS hA in
/-- **Induction**, read, for every predicate definable in `LXJ` with parameters. -/
theorem ind_of_eval_definable
    (h : ∀ F, Semiformula.Eval (s := s) ![] Empty.elim (indAxJ A F))
    (y : N) {P : N → Prop} (hP : LXJ.DefinablePred P)
    (hprog : ∀ x, R P (lowJ y) y x → P x) : ∀ x, Jm y x → P x := by
  have : Inhabited N := ⟨0⟩
  obtain ⟨ψ, f, hψ⟩ := natFormula_of_definable hP
  obtain ⟨F, hF⟩ : ∃ F : Semiformula LXJ ℕ 2,
      ∀ t, Semiformula.Eval (s := s) ![t, y] f F ↔ P t := by
    refine ⟨ψ ⇜ ![(#0 : Semiterm LXJ ℕ 2)], fun t => ?_⟩
    rw [Semiformula.eval_substs]
    have hc : (Semiterm.val (s := s) ![t, y] f ∘ ![(#0 : Semiterm LXJ ℕ 2)] : Fin 1 → N) =
        ![t] := by
      funext i; fin_cases i; rfl
    rw [hc, hψ]
  have hPF : (fun t => Semiformula.Eval (s := s) ![t, y] f F) = P :=
    funext fun t => propext (hF t)
  intro x hx
  have key := ind_of_eval hS A R hA F (h F) f y ?_ x hx
  · exact (hF x).mp key
  · intro z hz
    rw [hPF] at hz
    exact (hF z).mpr (hprog z hz)

end Axioms

/-! ### With the internal order -/

section Concrete

variable {N : Type} [ORingStructure N] [N↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [s : Structure LXJ N]

/-- The field: normal domain codes. -/
def fldW (x : N) : Prop := isNF x ∧ isDom x

/-- **`D_k`**: codes of the field whose coefficients of every level `j < k` are in `J(j, ·)`. -/
def DkW (k x : N) : Prop := fldW x ∧ ∀ j < k, ∀ δ, iinE j δ x = 1 → Jm j δ

/-- **The form of level `k`, read**, with `P` for the level's own place:
`D_k(x) ∧ x ≺ Ω_{k+1} ∧ ∀z ∈ D_k, z ≺ x → P z`. -/
def AccW (k : N) (P : N → Prop) (x : N) : Prop :=
  DkW k x ∧ iltb x (tcOmega k) = 1 ∧ ∀ z, DkW k z → iltb z x = 1 → P z

omit [s : Structure LXJ N] in
theorem eval_iltDefW (x y : N) : iltDefW.val.Evalb ![x, y] ↔ iltb x y = 1 := by
  exact OrdinalAnalysis.eval_wrap2 iltbDef iltb x y

theorem dcR_c_iff (y x : N) : DcR (lowJ y) thNFDef thDomDef y x ↔ DkW y x := by
  unfold DcR DkW FldR fldW lowJ
  rw [eval_thNFDef, eval_thDomDef]
  exact and_congr Iff.rfl (forall_congr' fun j => forall_congr' fun hj => forall_congr' fun δ =>
    imp_congr_right fun _ => and_iff_right hj)

/-- **The concrete form, read**: `AccR` for `WFormWc` is `AccW`. -/
theorem accR_c_iff (P : N → Prop) (y x : N) :
    AccR P (lowJ y) iltDefW thNFDef thDomDef y x ↔ AccW y P x := by
  unfold AccR AccW LtR
  simp only [dcR_c_iff, eval_iltDefW]

/-- **Closure of `WFormWc`**, read with the internal order. -/
theorem closure_c_of_eval (hS : s.lMap toLXJ = Arithmetic.standardModel N)
    (h : Semiformula.Eval (s := s) ![] Empty.elim (closureAxJ WFormWc)) (k x : N)
    (hx : AccW k (Jm k) x) : Jm k x :=
  closure_of_eval hS WFormWc (fun Pr Qr y x => AccR Pr Qr iltDefW thNFDef thDomDef y x)
    (fun Pr Qr x y => eval_WFormW Pr Qr _ _ _ x y) h k x ((accR_c_iff _ k x).mpr hx)

/-- **Induction of `WFormWc`** for definable predicates, read with the internal order. -/
theorem ind_c_of_eval (hS : s.lMap toLXJ = Arithmetic.standardModel N)
    (h : ∀ F, Semiformula.Eval (s := s) ![] Empty.elim (indAxJ WFormWc F))
    (k : N) {P : N → Prop} (hP : LXJ.DefinablePred P) (hprog : ∀ x, AccW k P x → P x) :
    ∀ x, Jm k x → P x :=
  ind_of_eval_definable hS WFormWc (fun Pr Qr y x => AccR Pr Qr iltDefW thNFDef thDomDef y x)
    (fun Pr Qr x y => eval_WFormW Pr Qr _ _ _ x y) h k hP
    fun x hx => hprog x ((accR_c_iff P k x).mp hx)

end Concrete

end OrdinalAnalysis.IDw.Upper
