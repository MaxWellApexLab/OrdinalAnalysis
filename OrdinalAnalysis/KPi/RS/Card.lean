import OrdinalAnalysis.KPi.RS.Infty

/-!
# The RS calculus, part 5: `TermReg` from regularity of a cardinal

For `kappa = c.ord` with `c` a regular cardinal `> aleph_0`, `TermReg kappa` holds.  The only real
content is the cardinality bound `#(T_a) < c` for `a < kappa`, proved by an injective prefix code of
the terms of level `< a` into `List Tk` (`Tk` a record `<tag, a, b, x>`, `x` the only ordinal label).
`RegOrd` is the class of these `kappa` (B92 Sect. 4: `R` consists of uncountable regular cardinals) and
`truth_lemma_regular` is the Truth Lemma with that hypothesis on `R` only.
-/

open Ordinal Cardinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

/-- tokens of the prefix code; `x` is the (only) ordinal label. -/
structure Tk : Type 2 where
  tag : ℕ
  a : ℕ
  b : ℕ
  x : Ordinal.{1}

/-- prefix code of an RS-formula. -/
def codeD : {n : ℕ} → D0 n → List Tk
  | _, .mem i j => [⟨0, i.val, j.val, 0⟩]
  | _, .nmem i j => [⟨1, i.val, j.val, 0⟩]
  | _, .ad i => [⟨2, i.val, 0, 0⟩]
  | _, .nad i => [⟨3, i.val, 0, 0⟩]
  | _, .and A B => ⟨4, 0, 0, 0⟩ :: (codeD A ++ codeD B)
  | _, .or A B => ⟨5, 0, 0, 0⟩ :: (codeD A ++ codeD B)
  | _, .bex (.var i) A => ⟨6, i.val, 0, 0⟩ :: codeD A
  | _, .bex (.lev γ) A => ⟨7, 0, 0, γ⟩ :: codeD A
  | _, .ball (.var i) A => ⟨8, i.val, 0, 0⟩ :: codeD A
  | _, .ball (.lev γ) A => ⟨9, 0, 0, γ⟩ :: codeD A

theorem codeD_prefix : ∀ {n : ℕ} (A A' : D0 n) (l l' : List Tk),
    codeD A ++ l = codeD A' ++ l' → A = A' ∧ l = l' := by
  intro n A
  induction A with
  | mem i j =>
    intro A' l l' h
    cases A' <;> simp [codeD] at h <;> (try cases ‹Bd _›) <;> simp_all [codeD, Fin.ext_iff]
  | nmem i j =>
    intro A' l l' h
    cases A' <;> simp [codeD] at h <;> (try cases ‹Bd _›) <;> simp_all [codeD, Fin.ext_iff]
  | ad i =>
    intro A' l l' h
    cases A' <;> simp [codeD] at h <;> (try cases ‹Bd _›) <;> simp_all [codeD, Fin.ext_iff]
  | nad i =>
    intro A' l l' h
    cases A' <;> simp [codeD] at h <;> (try cases ‹Bd _›) <;> simp_all [codeD, Fin.ext_iff]
  | and A B ihA ihB =>
    intro A' l l' h
    cases A' with
    | and A' B' =>
      simp only [codeD, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨rfl, h2⟩ := ihA A' _ _ h
      obtain ⟨rfl, rfl⟩ := ihB B' _ _ h2
      exact ⟨rfl, rfl⟩
    | bex b X => cases b <;> simp [codeD] at h
    | ball b X => cases b <;> simp [codeD] at h
    | _ => simp [codeD] at h
  | or A B ihA ihB =>
    intro A' l l' h
    cases A' with
    | or A' B' =>
      simp only [codeD, List.cons_append, List.cons.injEq, List.append_assoc, true_and] at h
      obtain ⟨rfl, h2⟩ := ihA A' _ _ h
      obtain ⟨rfl, rfl⟩ := ihB B' _ _ h2
      exact ⟨rfl, rfl⟩
    | bex b X => cases b <;> simp [codeD] at h
    | ball b X => cases b <;> simp [codeD] at h
    | _ => simp [codeD] at h
  | bex b A ih =>
    intro A' l l' h
    cases b with
    | var i =>
      cases A' with
      | bex b' X =>
        cases b' with
        | var i' =>
          simp only [codeD, List.cons_append, List.cons.injEq, Tk.mk.injEq] at h
          obtain ⟨⟨-, hi, -, -⟩, h2⟩ := h
          obtain ⟨rfl, rfl⟩ := ih X _ _ h2
          exact ⟨by rw [Fin.ext hi], rfl⟩
        | lev γ => simp [codeD] at h
      | ball b' X => cases b' <;> simp [codeD] at h
      | _ => simp [codeD] at h
    | lev γ =>
      cases A' with
      | bex b' X =>
        cases b' with
        | var i' => simp [codeD] at h
        | lev γ' =>
          simp only [codeD, List.cons_append, List.cons.injEq, Tk.mk.injEq] at h
          obtain ⟨⟨-, -, -, hγ⟩, h2⟩ := h
          obtain ⟨rfl, rfl⟩ := ih X _ _ h2
          exact ⟨by rw [hγ], rfl⟩
      | ball b' X => cases b' <;> simp [codeD] at h
      | _ => simp [codeD] at h
  | ball b A ih =>
    intro A' l l' h
    cases b with
    | var i =>
      cases A' with
      | ball b' X =>
        cases b' with
        | var i' =>
          simp only [codeD, List.cons_append, List.cons.injEq, Tk.mk.injEq] at h
          obtain ⟨⟨-, hi, -, -⟩, h2⟩ := h
          obtain ⟨rfl, rfl⟩ := ih X _ _ h2
          exact ⟨by rw [Fin.ext hi], rfl⟩
        | lev γ => simp [codeD] at h
      | bex b' X => cases b' <;> simp [codeD] at h
      | _ => simp [codeD] at h
    | lev γ =>
      cases A' with
      | ball b' X =>
        cases b' with
        | var i' => simp [codeD] at h
        | lev γ' =>
          simp only [codeD, List.cons_append, List.cons.injEq, Tk.mk.injEq] at h
          obtain ⟨⟨-, -, -, hγ⟩, h2⟩ := h
          obtain ⟨rfl, rfl⟩ := ih X _ _ h2
          exact ⟨by rw [hγ], rfl⟩
      | bex b' X => cases b' <;> simp [codeD] at h
      | _ => simp [codeD] at h

/-- prefix code of an RS-term: head token `⟨11, n, 0, β⟩`, then the code of the body, then the parameters. -/
def codePT : PT → List Tk
  | .L β => [⟨10, 0, 0, β⟩]
  | .sep β (n := n) φ a =>
      ⟨11, n, 0, β⟩ :: (codeD φ ++ (List.ofFn fun i => codePT (a i)).flatten)

theorem kids_prefix : ∀ (n : ℕ) (a a' : Fin n → PT),
    (∀ i, ∀ (t' : PT) (l l' : List Tk), codePT (a i) ++ l = codePT t' ++ l' → a i = t' ∧ l = l') →
    ∀ l l' : List Tk, (List.ofFn fun i => codePT (a i)).flatten ++ l =
      (List.ofFn fun i => codePT (a' i)).flatten ++ l' → a = a' ∧ l = l' := by
  intro n
  induction n with
  | zero =>
    intro a a' _ l l' h
    simp at h
    exact ⟨funext (fun i => i.elim0), h⟩
  | succ n ih =>
    intro a a' hA l l' h
    simp only [List.ofFn_succ, List.flatten_cons, List.append_assoc] at h
    obtain ⟨h1, h2⟩ := hA 0 (a' 0) _ _ h
    obtain ⟨h3, h4⟩ := ih (fun i => a i.succ) (fun i => a' i.succ) (fun i => hA i.succ) _ _ h2
    refine ⟨funext fun i => ?_, h4⟩
    induction i using Fin.cases with
    | zero => exact h1
    | succ j => exact congrFun h3 j

theorem codePT_prefix : ∀ (t t' : PT) (l l' : List Tk), codePT t ++ l = codePT t' ++ l' →
    t = t' ∧ l = l' := by
  intro t
  induction t with
  | L β =>
    intro t' l l' h
    cases t' with
    | L β' =>
      simp only [codePT, List.cons_append, List.nil_append, List.cons.injEq, Tk.mk.injEq] at h
      obtain ⟨⟨-, -, -, hβ⟩, h2⟩ := h
      subst hβ; subst h2; exact ⟨rfl, rfl⟩
    | sep β' φ' a' => simp [codePT] at h
  | sep β φ a ih =>
    intro t' l l' h
    cases t' with
    | L β' => simp [codePT] at h
    | sep β' φ' a' =>
      rename_i n n'
      simp only [codePT, List.cons_append, List.cons.injEq, Tk.mk.injEq] at h
      obtain ⟨⟨-, hn, -, hβ⟩, h2⟩ := h
      subst hn
      subst hβ
      rw [List.append_assoc, List.append_assoc] at h2
      obtain ⟨rfl, h3⟩ := codeD_prefix φ φ' _ _ h2
      obtain ⟨rfl, h4⟩ := kids_prefix _ a a' ih _ _ h3
      exact ⟨rfl, h4⟩

/-! ### tokens carry only labels `< α` -/

theorem codeD_lt : ∀ {n : ℕ} (A : D0 n) (α β : Ordinal.{1}), β < α → D0.LevLE β A →
    ∀ tk ∈ codeD A, tk.x < α := by
  intro n A α β hβ
  have h0 : (0 : Ordinal.{1}) < α := lt_of_le_of_lt zero_le hβ
  induction A with
  | mem i j => intro _ tk htk; simp only [codeD, List.mem_singleton] at htk; subst htk; exact h0
  | nmem i j => intro _ tk htk; simp only [codeD, List.mem_singleton] at htk; subst htk; exact h0
  | ad i => intro _ tk htk; simp only [codeD, List.mem_singleton] at htk; subst htk; exact h0
  | nad i => intro _ tk htk; simp only [codeD, List.mem_singleton] at htk; subst htk; exact h0
  | and A B ihA ihB =>
    intro hL tk htk
    simp only [D0.LevLE] at hL
    simp only [codeD, List.mem_cons, List.mem_append] at htk
    rcases htk with rfl | htk | htk
    · exact h0
    · exact ihA hL.1 tk htk
    · exact ihB hL.2 tk htk
  | or A B ihA ihB =>
    intro hL tk htk
    simp only [D0.LevLE] at hL
    simp only [codeD, List.mem_cons, List.mem_append] at htk
    rcases htk with rfl | htk | htk
    · exact h0
    · exact ihA hL.1 tk htk
    · exact ihB hL.2 tk htk
  | bex b A ih =>
    intro hL tk htk
    cases b with
    | var i =>
      simp only [D0.LevLE] at hL
      simp only [codeD, List.mem_cons] at htk
      rcases htk with rfl | htk
      · exact h0
      · exact ih hL tk htk
    | lev γ =>
      simp only [D0.LevLE] at hL
      simp only [codeD, List.mem_cons] at htk
      rcases htk with rfl | htk
      · exact lt_of_le_of_lt hL.1 hβ
      · exact ih hL.2 tk htk
  | ball b A ih =>
    intro hL tk htk
    cases b with
    | var i =>
      simp only [D0.LevLE] at hL
      simp only [codeD, List.mem_cons] at htk
      rcases htk with rfl | htk
      · exact h0
      · exact ih hL tk htk
    | lev γ =>
      simp only [D0.LevLE] at hL
      simp only [codeD, List.mem_cons] at htk
      rcases htk with rfl | htk
      · exact lt_of_le_of_lt hL.1 hβ
      · exact ih hL.2 tk htk

theorem codePT_lt : ∀ (t : PT), t.Wf → ∀ α : Ordinal.{1}, t.level < α →
    ∀ tk ∈ codePT t, tk.x < α
  | .L β, _, α, h, tk, htk => by
      simp only [codePT, List.mem_singleton] at htk
      subst htk
      exact h
  | .sep β φ a, hw, α, h, tk, htk => by
      obtain ⟨h0, hL, ha, hOcc⟩ := hw
      have hβ : β < α := h
      simp only [codePT, List.mem_cons, List.mem_append, List.mem_flatten, List.mem_ofFn] at htk
      rcases htk with rfl | htk | ⟨s, ⟨i, rfl⟩, hs⟩
      · exact hβ
      · exact codeD_lt φ α β hβ hL tk htk
      · exact codePT_lt (a i) (ha i).1 α (lt_trans (ha i).2 hβ) tk hs

/-! ### the cardinality bound -/

theorem card_Tlt_le (α : Ordinal.{1}) :
    #(Tlt α) ≤ max ℵ₀ (ℵ₀ * (ℵ₀ * (ℵ₀ * #(Set.Iio α)))) := by
  let f : Tlt α → List {tk : Tk // tk.x < α} := fun t =>
    (codePT t.1.1).pmap (fun tk h => ⟨tk, h⟩) (codePT_lt t.1.1 t.1.2 α t.2)
  have hf : Function.Injective f := by
    intro t t' h
    have h1 : (f t).map Subtype.val = (f t').map Subtype.val := by rw [h]
    simp only [f, List.map_pmap, List.pmap_eq_map, List.map_id'] at h1
    have h2 := (codePT_prefix _ _ [] [] (by simpa using h1)).1
    exact Subtype.ext (Subtype.ext h2)
  have h1 : #(Tlt α) ≤ #(List {tk : Tk // tk.x < α}) := Cardinal.mk_le_of_injective hf
  have h2 := Cardinal.mk_list_le_max {tk : Tk // tk.x < α}
  have h3 : #{tk : Tk // tk.x < α} ≤ ℵ₀ * (ℵ₀ * (ℵ₀ * #(Set.Iio α))) := by
    let g : {tk : Tk // tk.x < α} → ULift.{2} ℕ × ULift.{2} ℕ × ULift.{2} ℕ × Set.Iio α :=
      fun tk => (⟨tk.1.tag⟩, ⟨tk.1.a⟩, ⟨tk.1.b⟩, ⟨tk.1.x, tk.2⟩)
    have hg : Function.Injective g := by
      rintro ⟨⟨a1, a2, a3, a4⟩, h⟩ ⟨⟨b1, b2, b3, b4⟩, h'⟩ e
      have e1 := congrArg (fun p => p.1.down) e
      have e2 := congrArg (fun p => p.2.1.down) e
      have e3 := congrArg (fun p => p.2.2.1.down) e
      have e4 := congrArg (fun p => (p.2.2.2 : Ordinal.{1})) e
      simp only [g] at e1 e2 e3 e4
      subst e1 e2 e3 e4
      rfl
    refine (Cardinal.mk_le_of_injective hg).trans (le_of_eq ?_)
    simp [Cardinal.mk_prod]
  exact h1.trans (h2.trans (max_le_max le_rfl h3))

theorem card_Tlt_lt {c : Cardinal.{1}} (hc : ℵ₀ < c) {α : Ordinal.{1}} (hα : α < c.ord) :
    #(Tlt α) < Cardinal.lift.{2} c := by
  refine lt_of_le_of_lt (card_Tlt_le α) ?_
  have hc' : ℵ₀ < Cardinal.lift.{2} c := by simpa using (Cardinal.lift_lt.{1, 2}).2 hc
  have hα' : Cardinal.lift.{2} α.card < Cardinal.lift.{2} c := (Cardinal.lift_lt).2 (Cardinal.lt_ord.1 hα)
  rw [Cardinal.mk_Iio_ordinal]
  refine max_lt hc' ?_
  exact Cardinal.mul_lt_of_lt hc'.le hc' (Cardinal.mul_lt_of_lt hc'.le hc' (Cardinal.mul_lt_of_lt hc'.le hc' hα'))

/-- **`TermReg` for regular cardinals**: for `c` a regular cardinal `> ℵ₀`, `TermReg c.ord`. -/
theorem termReg_of_regular {c : Cardinal.{1}} (hc : c.IsRegular) (h0 : ℵ₀ < c) : TermReg c.ord := by
  refine ⟨Cardinal.isSuccLimit_ord h0.le, ?_⟩
  intro α hα f hf
  have hcard := card_Tlt_lt h0 hα
  have ha : Cardinal.lift.{1} #(Tlt α) < (Ordinal.lift.{2} c.ord).cof := by
    rw [← Ordinal.lift_cof, hc.cof_ord, Cardinal.lift_id'.{1, 2}]
    exact hcard
  have hsup : ⨆ t, f t < c.ord := Ordinal.lift_iSup_lt_of_lt_cof ha hf
  refine ⟨⨆ t, f t, hsup, fun t => ?_⟩
  exact le_ciSup ⟨c.ord, by rintro _ ⟨t, rfl⟩; exact (hf t).le⟩ t

/-- the ordinals `κ = c.ord` of regular cardinals `c > ℵ₀` (B92 §4: `R` is a class of uncountable regular cardinals). -/
def RegOrd : Set Ordinal.{1} := {κ | ∃ c : Cardinal.{1}, c.IsRegular ∧ ℵ₀ < c ∧ κ = c.ord}

/-- **Truth Lemma 3.2, hypothesis-free form**: if `R` consists of ordinals of uncountable regular
cardinals, every `RS^∞`-derivable sequent is true. -/
theorem truth_lemma_regular (R : Set Ordinal.{1}) (hR : R ⊆ RegOrd) {Γ : Set RSS}
    {α ρ : Ordinal.{1}} (h : Inf R Γ α ρ) : ∃ A ∈ Γ, RSTrue R A := by
  refine truth_lemma R (fun κ hκ => ?_) h
  obtain ⟨c, hc, h0, rfl⟩ := hR hκ
  exact termReg_of_regular hc h0

end OrdinalAnalysis.KPi.RS
