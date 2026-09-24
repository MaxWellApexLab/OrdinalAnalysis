/-
  The coding of the ϑ-notation in the standard model.

  In `ℕ` the recognisers of `Codes` accept exactly the codes of terms and of normal forms, so
  the arithmetic formulas mean what they say:

  * `thTermDef` holds of `n` iff `n = code t` for a term `t`, and then `decode n = t`;
  * `thNFDef` holds of `n` iff `n = code t` for a normal form `t`;
  * `thLenDef`, `thInEDef`, `thLtDef` are `l`, membership in `E` and `≺` on codes;
  * `thPrecDef` is the order of `ThetaNote` on codes, and relates only codes of notations;
  * `thPrecFieldDef` is the order of the notations below `Ω`, and relates only their codes.

  The last two are packaged as coded orderings (`Gentzen.CodedOrder`) on `ThetaNote` and on
  the notations below `Ω`, with the formulas transported into the language `LX`.
-/
import OrdinalAnalysis.ID1.Internal.Codes
import OrdinalAnalysis.Gentzen.CodedOrder

set_option autoImplicit false

namespace OrdinalAnalysis.ID1.Internal

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open OrdinalAnalysis.Gentzen
open OrdinalAnalysis.Gentzen.CodedNotation (liftCode)
open OrdinalAnalysis.Gentzen.StandardLX (stdLX eval_lMap_toLX)
open OrdinalAnalysis.ThetaTerm

/-! ## Codes as numbers -/

theorem code_theta' (a : ThetaTerm) : code (.theta a) = tcTheta (V := ℕ) (code a) := by
  have h := mc_theta (V := ℕ) a
  simp only [mc_nat] at h
  exact h

theorem code_cons' (x : ThetaTerm) (xs : List ThetaTerm) :
    code (.sum (x :: xs)) = tcCons (V := ℕ) (code x) (code (.sum xs)) := by
  have h := mc_cons (V := ℕ) x xs
  simp only [mc_nat] at h
  exact h

/-- **Every number the term recogniser accepts is the code of a term.** -/
theorem isTerm_surj (n : ℕ) (h : isTerm n) : ∃ t : ThetaTerm, code t = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold isTerm at h
    rcases kind_cases n with hk | hk | hk | hk | hk
    · exact ⟨.sum [], by rw [code_nil, (kind_eq_zero_iff.mp hk)]⟩
    · rw [isTermb_kind_one hk, beq_eq_one] at h
      exact ⟨.Omega, by rw [code_Omega, eq_one_of_kind hk h]⟩
    · rw [eq_tcTheta_of_kind hk, isTermb_tcTheta] at h
      have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      obtain ⟨a, ha⟩ := ih _ (tcArg_lt hn0) h
      exact ⟨.theta a, by rw [code_theta', ha, ← eq_tcTheta_of_kind hk]⟩
    · rw [eq_tcCons_of_kind hk, isTermb_tcCons, band_eq_one, band_eq_one] at h
      obtain ⟨h1, h2, h3⟩ := h
      have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      obtain ⟨x, hx⟩ := ih _ (tcHd_lt hn0) h1
      obtain ⟨u, hu⟩ := ih _ (tcTl_lt hn0) h2
      cases u with
      | Omega => rw [← hu, code_Omega] at h3; simp at h3
      | theta b => rw [← hu, code_theta'] at h3; simp at h3
      | sum ys =>
        exact ⟨.sum (x :: ys), by rw [code_cons', hx, hu, ← eq_tcCons_of_kind hk]⟩
    · rw [isTermb_kind_four hk] at h; simp at h

theorem isTerm_iff (n : ℕ) : isTerm n ↔ ∃ t : ThetaTerm, code t = n := by
  refine ⟨isTerm_surj n, ?_⟩
  rintro ⟨t, rfl⟩
  simpa using isTerm_mc (V := ℕ) t

/-- **Coding inverts decoding on codes.** -/
theorem code_decode {n : ℕ} (h : isTerm n) : code (decode n) = n := by
  obtain ⟨t, rfl⟩ := isTerm_surj n h
  rw [decode_code]

/-- The hereditary part of normality already forces the shape of a term. -/
theorem isTerm_of_nfA (n : ℕ) (h : nfA n = 1) : isTerm n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    unfold isTerm
    rcases kind_cases n with hk | hk | hk | hk | hk
    · rw [kind_eq_zero_iff.mp hk]; simp
    · rw [nfA_kind_one hk] at h; rw [isTermb_kind_one hk]; exact h
    · have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      rw [eq_tcTheta_of_kind hk] at h ⊢
      rw [nfA_tcTheta, isNFb, band_eq_one] at h
      rw [isTermb_tcTheta]
      exact ih _ (tcArg_lt hn0) h.1
    · have hn0 : n ≠ 0 := fun e => by simp [e] at hk
      rw [eq_tcCons_of_kind hk] at h ⊢
      rw [nfA_tcCons, isNFb] at h
      simp only [band_eq_one] at h
      rw [isTermb_tcCons, band_eq_one, band_eq_one]
      exact ⟨ih _ (tcHd_lt hn0) h.1.1, ih _ (tcTl_lt hn0) h.2.1, h.2.2.1⟩
    · rw [nfA_kind_four hk] at h; simp at h

/-- **Every number the normal-form recogniser accepts is the code of a normal form.** -/
theorem isNF_surj (n : ℕ) (h : isNF n) : ∃ t : ThetaTerm, NF t ∧ code t = n := by
  have hn : nfA n = 1 := (band_eq_one.mp h).1
  obtain ⟨t, rfl⟩ := isTerm_surj n (isTerm_of_nfA n hn)
  exact ⟨t, (isNF_mc (V := ℕ) t).mp (by simpa using h), rfl⟩

theorem isNF_iff (n : ℕ) : isNF n ↔ ∃ t : ThetaTerm, NF t ∧ code t = n := by
  refine ⟨isNF_surj n, ?_⟩
  rintro ⟨t, ht, rfl⟩
  simpa using (isNF_mc (V := ℕ) t).mpr ht

/-! ## The formulas in `ℕ` -/

theorem eval_thTermDef_nat (n : ℕ) : thTermDef.val.Evalb ![n] ↔ ∃ t : ThetaTerm, code t = n := by
  rw [eval_thTermDef, isTerm_iff]

theorem eval_thNFDef_nat (n : ℕ) :
    thNFDef.val.Evalb ![n] ↔ ∃ t : ThetaTerm, NF t ∧ code t = n := by
  rw [eval_thNFDef, isNF_iff]

theorem eval_thNFDef_code (t : ThetaTerm) : thNFDef.val.Evalb ![code t] ↔ NF t := by
  simpa using eval_thNFDef_mc (V := ℕ) t

theorem eval_thLenDef_code (m : ℕ) (t : ThetaTerm) :
    thLenDef.val.Evalb ![m, code t] ↔ m = l t := by
  rw [eval_thLenDef]
  have h := ilen_mc (V := ℕ) t
  simp only [mc_nat] at h
  rw [h]
  simp

theorem eval_thInEDef_code (g a : ThetaTerm) :
    thInEDef.val.Evalb ![code g, code a] ↔ g ∈ E a := by
  simpa using eval_thInEDef_mc (V := ℕ) g a

theorem eval_thLtDef_code (y x : ThetaTerm) :
    thLtDef.val.Evalb ![code y, code x] ↔ y < x := by
  simpa using eval_thLtDef_mc (V := ℕ) y x

theorem eval_thCmpDef_code (m : ℕ) (a b : ThetaTerm) :
    thCmpDef.val.Evalb ![m, code a, code b] ↔
      (m = 0 ∧ a < b) ∨ (m = 1 ∧ a = b) ∨ (m = 2 ∧ b < a) := by
  rw [eval_thCmpDef]
  have h0 := icmp_mc_eq_zero_iff (V := ℕ) a b
  have h1 := icmp_mc_eq_one_iff (V := ℕ) a b
  have h2 := icmp_mc_eq_two_iff (V := ℕ) a b
  simp only [mc_nat] at h0 h1 h2
  rcases lt_trichotomy' a b with h | h | h
  · have e := h0.mpr h
    rw [e]
    constructor
    · rintro rfl; exact Or.inl ⟨rfl, h⟩
    · rintro (⟨rfl, -⟩ | ⟨rfl, h'⟩ | ⟨rfl, h'⟩)
      · rfl
      · exact absurd h' (ne_of_lt' h)
      · exact absurd h' (lt_asymm' h)
  · have e := h1.mpr h
    rw [e]
    subst h
    constructor
    · rintro rfl; exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · rintro (⟨rfl, h'⟩ | ⟨rfl, -⟩ | ⟨rfl, h'⟩)
      · exact absurd h' (lt_irrefl' a)
      · rfl
      · exact absurd h' (lt_irrefl' a)
  · have e := h2.mpr h
    rw [e]
    constructor
    · rintro rfl; exact Or.inr (Or.inr ⟨rfl, h⟩)
    · rintro (⟨rfl, h'⟩ | ⟨rfl, h'⟩ | ⟨rfl, -⟩)
      · exact absurd h' (lt_asymm' h)
      · exact absurd h'.symm (ne_of_lt' h)
      · rfl

/-! ## The order of the notations, read in `ℕ` -/

/-- `m ≺ n` on numbers: the order formula read in `ℕ`. -/
def precN (m n : ℕ) : Prop := thPrecDef.val.Evalb ![m, n]

theorem precN_iff (m n : ℕ) : precN m n ↔ isNF m ∧ isNF n ∧ iltb m n = 1 :=
  eval_thPrecDef (V := ℕ) m n

/-- **Standard codes are ordered as the notations are.** -/
theorem precN_codeNote_iff (a b : ThetaNote) : precN (codeNote a) (codeNote b) ↔ a < b := by
  unfold precN codeNote
  rw [show a < b ↔ a.1 < b.1 from Iff.rfl]
  simpa [a.2, b.2] using eval_thPrecDef_mc (V := ℕ) a.1 b.1

/-- **The order relates only codes of notations.** -/
theorem precN_exists_lt {m n : ℕ} (h : precN m n) :
    ∃ a b : ThetaNote, codeNote a = m ∧ codeNote b = n ∧ a < b := by
  obtain ⟨hm, hn, -⟩ := (precN_iff m n).mp h
  obtain ⟨y, hy, rfl⟩ := isNF_surj m hm
  obtain ⟨x, hx, rfl⟩ := isNF_surj n hn
  exact ⟨⟨y, hy⟩, ⟨x, hx⟩, rfl, rfl, (precN_codeNote_iff ⟨y, hy⟩ ⟨x, hx⟩).mp h⟩

/-! ## The order below `Ω`, read in `ℕ` -/

/-- The notations below `Ω`: the field of the accessibility order. -/
abbrev ThetaField : Type := {a : ThetaNote // a < ThetaNote.Omega}

/-- The code of a notation below `Ω`. -/
def codeField (a : ThetaField) : ℕ := codeNote a.1

/-- `n` is in the field: the code of a notation below `Ω`. -/
def fieldN (n : ℕ) : Prop := thFieldDef.val.Evalb ![n]

/-- `m ≺ n` on numbers, both in the field. -/
def precFieldN (m n : ℕ) : Prop := thPrecFieldDef.val.Evalb ![m, n]

/-- **The field is exactly the set of codes of the notations below `Ω`.** -/
theorem fieldN_iff (n : ℕ) : fieldN n ↔ ∃ a : ThetaField, codeField a = n := by
  unfold fieldN
  rw [eval_thFieldDef]
  constructor
  · rintro ⟨hn, hlt⟩
    obtain ⟨x, hx, rfl⟩ := isNF_surj n hn
    have : x < .Omega := (iltb_mc_one (V := ℕ) x).mp (by simpa using hlt)
    exact ⟨⟨⟨x, hx⟩, this⟩, rfl⟩
  · rintro ⟨a, rfl⟩
    simpa [codeField, codeNote] using (eval_thFieldDef_mc (V := ℕ) a.1.1).mpr ⟨a.1.2, a.2⟩

theorem precFieldN_codeField_iff (a b : ThetaField) :
    precFieldN (codeField a) (codeField b) ↔ a < b := by
  unfold precFieldN codeField codeNote
  have h := eval_thPrecFieldDef_mc (V := ℕ) a.1.1 b.1.1
  simp only [mc_nat] at h
  rw [h]
  have ha : a.1.1 < ThetaTerm.Omega := a.2
  have hb : b.1.1 < ThetaTerm.Omega := b.2
  simp only [a.1.2, b.1.2, ha, hb, true_and]
  rfl

/-- **The order below `Ω` relates only codes of notations below `Ω`.** -/
theorem precFieldN_exists_lt {m n : ℕ} (h : precFieldN m n) :
    ∃ a b : ThetaField, codeField a = m ∧ codeField b = n ∧ a < b := by
  have h' := h
  unfold precFieldN at h'
  rw [eval_thPrecFieldDef] at h'
  obtain ⟨hm, hn, -⟩ := h'
  obtain ⟨a, rfl⟩ := (fieldN_iff m).mp (by unfold fieldN; rw [eval_thFieldDef]; exact hm)
  obtain ⟨b, rfl⟩ := (fieldN_iff n).mp (by unfold fieldN; rw [eval_thFieldDef]; exact hn)
  exact ⟨a, b, rfl, rfl, (precFieldN_codeField_iff a b).mp h⟩

/-! ## The coded orderings, in `LX` -/

/-- The order of the notations as a formula of `LX`. -/
def precCodeTheta : Semiformula LX ℕ 2 := liftCode thPrecDef.val

/-- The order below `Ω` as a formula of `LX`. -/
def precCodeField : Semiformula LX ℕ 2 := liftCode thPrecFieldDef.val

@[simp] theorem XFree_precCodeTheta : LowerClass.XFree precCodeTheta :=
  LowerClass.XFree_lMap_toLX _

@[simp] theorem XFree_precCodeField : LowerClass.XFree precCodeField :=
  LowerClass.XFree_lMap_toLX _

@[simp] theorem freeVariables_precCodeTheta : precCodeTheta.freeVariables = ∅ := by
  simp [precCodeTheta, liftCode]

@[simp] theorem freeVariables_precCodeField : precCodeField.freeVariables = ∅ := by
  simp [precCodeField, liftCode]

/-- A formula transported from arithmetic, at a pair of numerals, in the standard structure. -/
theorem eval_precAt_liftCode_numeral (σ : ArithmeticSemisentence 2) (P : ℕ → Prop)
    (m n : ℕ) (f : ℕ → ℕ) :
    Semiformula.Eval (s := stdLX P) ![] f
      (precAt (liftCode σ) (LowerSyntax.numLX m) (LowerSyntax.numLX n)) ↔
        σ.Evalb ![m, n] := by
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
  unfold liftCode
  rw [eval_lMap_toLX]
  simp

/-- **The coded ordering of the ϑ-notation**: the order of all normal forms. -/
def thetaOrder : CodedOrder ThetaNote where
  prec := precCodeTheta
  xfree_prec := XFree_precCodeTheta
  freeVariables_prec := freeVariables_precCodeTheta
  code := codeNote
  precN := precN
  eval_precAt_numeral := fun P m n f => eval_precAt_liftCode_numeral _ P m n f
  precN_code_iff := precN_codeNote_iff

/-- **The coded ordering of the notations below `Ω`.** -/
def thetaFieldOrder : CodedOrder ThetaField where
  prec := precCodeField
  xfree_prec := XFree_precCodeField
  freeVariables_prec := freeVariables_precCodeField
  code := codeField
  precN := precFieldN
  eval_precAt_numeral := fun P m n f => eval_precAt_liftCode_numeral _ P m n f
  precN_code_iff := precFieldN_codeField_iff

@[simp] theorem thetaOrder_code : thetaOrder.code = codeNote := rfl

@[simp] theorem thetaOrder_precN : thetaOrder.precN = precN := rfl

@[simp] theorem thetaFieldOrder_code : thetaFieldOrder.code = codeField := rfl

@[simp] theorem thetaFieldOrder_precN : thetaFieldOrder.precN = precFieldN := rfl

end OrdinalAnalysis.ID1.Internal
