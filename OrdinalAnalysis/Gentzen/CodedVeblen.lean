/-
  The coded Veblen ordering: `precDef₁` transported into `LX`, read in `ℕ`, and packaged
  as a `CodedOrder Gamma0Note`.

  This is the `Γ₀` analogue of `Gentzen/CodedNotation.lean` (the transport) together with
  `Gentzen/PrecStandard.lean` (the reading in `ℕ`) and the `epsilon0Order` instance at the end
  of `Gentzen/CodedOrder.lean`.  Nothing here is new mathematics: `precDef₁` and its `Evalb`
  characterisation live in `InternalVNote`, the bridge to notations in `VNoteBridge`, and the
  four facts a `CodedOrder` asks for are exactly what those two supply.

  With `gamma0Order : CodedOrder Gamma0Note` in hand, the boundedness pipeline of
  `LowerClass`/`LowerClassEv`/`Boundedness`/`LowerBound` — generic over a coded ordering since
  the `coded-order` merge — can be run on the Veblen notations without further syntax work.
-/
import OrdinalAnalysis.Gentzen.VNoteBridge
import OrdinalAnalysis.Gentzen.CodedOrder
import OrdinalAnalysis.Gentzen.OmegaTruth

set_option autoImplicit false

namespace OrdinalAnalysis.Gentzen.CodedVeblen

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen.InternalVNote
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode)
open OrdinalAnalysis.Gentzen.VNoteBridge
open OrdinalAnalysis.Gentzen.StandardLX (stdLX eval_lMap_toLX)

/-! ## The formulas, in `LX` -/

/-- `x` is a Veblen normal form, as a formula of `LX`. -/
def nfCode₁ : Semiformula LX ℕ 1 := liftCode nfDef₁

/-- **The coded Veblen ordering** `≺₁`, as a formula of `LX` in two variables.  The `Γ₀`
analogue of `CodedNotation.precCode`. -/
def precCode₁ : Semiformula LX ℕ 2 := liftCode precDef₁

/-- Everything transported from arithmetic is `X`-free. -/
@[simp] theorem XFree_precCode₁ : LowerClass.XFree precCode₁ :=
  LowerClass.XFree_lMap_toLX _

@[simp] theorem XFree_nfCode₁ : LowerClass.XFree nfCode₁ :=
  LowerClass.XFree_lMap_toLX _

/-- The `OmegaTruth` spelling of the same fact (its atomic clause is `IsArithRel r`, not
`∃ r', r = Sum.inl r'`), for the ω-truth layer. -/
@[simp] theorem omegaTruth_XFree_precCode₁ : OmegaTruth.XFree precCode₁ :=
  OmegaTruth.xFree_lMap_toLX _

@[simp] theorem omegaTruth_XFree_nfCode₁ : OmegaTruth.XFree nfCode₁ :=
  OmegaTruth.xFree_lMap_toLX _

/-- `precCode₁` is closed: it is the `lMap`-image of the `emb` of an arithmetic sentence, and
both operations kill free variables. -/
@[simp] theorem freeVariables_precCode₁ : precCode₁.freeVariables = ∅ := by
  simp [precCode₁, liftCode]

@[simp] theorem freeVariables_nfCode₁ : nfCode₁.freeVariables = ∅ := by
  simp [nfCode₁, liftCode]

@[simp] theorem complexity_precCode₁ :
    precCode₁.complexity = (precDef₁.val : ArithmeticSemisentence 2).complexity := by
  simp [precCode₁, liftCode]

/-! ## The ordering read in `ℕ` -/

/-- `m ≺₁ n` on natural numbers: the coded Veblen ordering read in `ℕ`. -/
def precN₁ (m n : ℕ) : Prop := precDef₁.val.Evalb ![m, n]

theorem precN₁_iff (m n : ℕ) :
    precN₁ m n ↔ isNF₁ (V := ℕ) m ∧ isNF₁ (V := ℕ) n ∧ icmp₁ (V := ℕ) m n = 0 :=
  eval_precDef₁ (V := ℕ) m n

/-- `m` is a Veblen normal-form code, read in `ℕ`. -/
def nfN₁ (m : ℕ) : Prop := nfDef₁.val.Evalb ![m]

theorem nfN₁_iff (m : ℕ) : nfN₁ m ↔ isNF₁ (V := ℕ) m :=
  eval_nfDef₁ (V := ℕ) m

/-- **Standard Veblen codes are ordered as the notations are.**  The `Γ₀` analogue of
`PrecStandard.precN_code_iff`. -/
theorem precN₁_code_iff (a b : Gamma0Note) :
    precN₁ (gamma0Code a) (gamma0Code b) ↔ a < b := by
  rw [precN₁_iff]
  have hb := gamma0_lt_iff_icmp₁_eq_zero (V := ℕ) a b
  simp only [gamma0ModelCode_nat] at hb
  have ha' := isNF₁_gamma0ModelCode (V := ℕ) a
  have hb' := isNF₁_gamma0ModelCode (V := ℕ) b
  simp only [gamma0ModelCode_nat] at ha' hb'
  constructor
  · rintro ⟨-, -, h⟩; exact hb.mpr h
  · intro h; exact ⟨ha', hb', hb.mp h⟩

theorem precN₁_code_of_lt {a b : Gamma0Note} (h : a < b) :
    precN₁ (gamma0Code a) (gamma0Code b) :=
  (precN₁_code_iff a b).mpr h

theorem lt_of_precN₁_code {a b : Gamma0Note}
    (h : precN₁ (gamma0Code a) (gamma0Code b)) : a < b :=
  (precN₁_code_iff a b).mp h

/-! ## The syntactic bridge -/

/-- `precCode₁` evaluates in the standard structure as `precN₁`, whatever `X` is. -/
theorem eval_precCode₁ (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![m, n] f precCode₁ ↔ precN₁ m n := by
  unfold precCode₁ liftCode precN₁
  rw [eval_lMap_toLX]
  simp

/-- **The instance the boundedness induction meets**: `precAt precCode₁ (numLX m) (numLX n)`
says `m ≺₁ n`.  The `Γ₀` analogue of `PrecStandard.eval_precAt_numeral`. -/
theorem eval_precAt₁_numeral (P : ℕ → Prop) (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt precCode₁ (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔ precN₁ m n := by
  unfold precAt
  rw [Semiformula.eval_rew]
  have e₁ : (Semiterm.val (s := stdLX P) ![] f ∘
      ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.bvar) = ![m, n] := by
    have h : ∀ i : Fin 2, (Semiterm.val (s := stdLX P) ![] f ∘
        ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.bvar) i
          = ![m, n] i := by
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩ <;> simp
    funext i; exact h i
  have e₂ : (Semiterm.val (s := stdLX P) ![] f ∘
      ⇑(Rew.subst ![LowerSyntax.numLX m, LowerSyntax.numLX n]) ∘ Semiterm.fvar) = f := by
    funext x; simp
  rw [e₁, e₂]
  exact eval_precCode₁ P m n f

/-! ## The coded ordering of the Veblen notations

Every field is a definition or lemma already proved above; nothing is re-proved. -/

/-- **The coded ordering of the notations below `Γ₀`.**  This is what the ε₁ lower-bound
pipeline is instantiated at, exactly as `epsilon0Order` is the `ε₀` instance. -/
def gamma0Order : CodedOrder Gamma0Note where
  prec := precCode₁
  xfree_prec := XFree_precCode₁
  freeVariables_prec := freeVariables_precCode₁
  code := gamma0Code
  precN := precN₁
  eval_precAt_numeral := eval_precAt₁_numeral
  precN_code_iff := precN₁_code_iff

@[simp] theorem gamma0Order_prec : gamma0Order.prec = precCode₁ := rfl

@[simp] theorem gamma0Order_code : gamma0Order.code = gamma0Code := rfl

@[simp] theorem gamma0Order_precN : gamma0Order.precN = precN₁ := rfl

/-- The coded Veblen ordering never leaves the notations: both sides of `precN₁` decode
(`VNoteBridge.isNF₁_surj`). -/
theorem precN₁_dom {k n : ℕ} (h : precN₁ k n) :
    (∃ o : Gamma0Note, gamma0Code o = k) ∧ (∃ o : Gamma0Note, gamma0Code o = n) := by
  rw [precN₁_iff] at h
  exact ⟨isNF₁_surj k h.1, isNF₁_surj n h.2.1⟩

/-- The decoded witnesses of `precN₁_dom` are ordered as the notations are. -/
theorem precN₁_exists_lt {k n : ℕ} (h : precN₁ k n) :
    ∃ a b : Gamma0Note, gamma0Code a = k ∧ gamma0Code b = n ∧ a < b := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := precN₁_dom h
  exact ⟨a, b, ha, hb, (precN₁_code_iff a b).mp (by rw [ha, hb]; exact h)⟩

end OrdinalAnalysis.Gentzen.CodedVeblen
