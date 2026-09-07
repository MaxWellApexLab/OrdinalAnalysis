import OrdinalAnalysis.Ordinal.NaturalSumMono

namespace OrdinalAnalysis

private theorem cmp_eq_lt_of_lt {a b : ONote} (ha : ONote.NF a) (hb : ONote.NF b)
    (h : a < b) : a.cmp b = Ordering.lt := by
  have hc : (a.cmp b).Compares a b := @ONote.cmp_compares _ _ ha hb
  cases hab : a.cmp b <;> simp only [hab] at hc
  · rfl
  · exact (ne_of_lt h hc).elim
  · exact (not_lt_of_ge (le_of_lt hc) h).elim

private theorem cmp_eq_gt_of_gt {a b : ONote} (ha : ONote.NF a) (hb : ONote.NF b)
    (h : b < a) : a.cmp b = Ordering.gt := by
  exact cmp_eq_gt_iff.mpr (cmp_eq_lt_of_lt hb ha h)

private theorem nadd_oadd_of_lt {e₁ e₂ : ONote} {n₁ n₂ : ℕ+} {a₁ a₂ : ONote}
    (h : e₁.cmp e₂ = Ordering.lt) :
    nadd (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₂ n₂ a₂) =
      ONote.oadd e₂ n₂ (nadd (ONote.oadd e₁ n₁ a₁) a₂) := by
  rw [nadd.eq_def]
  simp only [h]

private theorem nadd_oadd_of_eq {e₁ e₂ : ONote} {n₁ n₂ : ℕ+} {a₁ a₂ : ONote}
    (h : e₁.cmp e₂ = Ordering.eq) :
    nadd (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₂ n₂ a₂) =
      ONote.oadd e₁ (n₁ + n₂) (nadd a₁ a₂) := by
  rw [nadd.eq_def]
  simp only [h]

private theorem nadd_oadd_of_gt {e₁ e₂ : ONote} {n₁ n₂ : ℕ+} {a₁ a₂ : ONote}
    (h : e₁.cmp e₂ = Ordering.gt) :
    nadd (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₂ n₂ a₂) =
      ONote.oadd e₁ n₁ (nadd a₁ (ONote.oadd e₂ n₂ a₂)) := by
  rw [nadd.eq_def]
  simp only [h]

theorem nadd_assoc : ∀ (a b c : ONote), ONote.NF a → ONote.NF b → ONote.NF c →
    nadd (nadd a b) c = nadd a (nadd b c)
  | 0, b, c, _, _, _ => by simp
  | ONote.oadd e₁ n₁ a₁, 0, c, _, _, _ => by simp
  | ONote.oadd e₁ n₁ a₁, ONote.oadd e₂ n₂ a₂, 0, _, _, _ => by simp
  | ONote.oadd e₁ n₁ a₁, ONote.oadd e₂ n₂ a₂, ONote.oadd e₃ n₃ a₃,
      h₁, h₂, h₃ => by
      have h₁₂ : ((e₁.cmp e₂).Compares e₁ e₂) :=
        @ONote.cmp_compares _ _ h₁.fst h₂.fst
      have h₂₃ : ((e₂.cmp e₃).Compares e₂ e₃) :=
        @ONote.cmp_compares _ _ h₂.fst h₃.fst
      cases hc₁₂ : e₁.cmp e₂ <;>
        cases hc₂₃ : e₂.cmp e₃ <;>
          simp only [hc₁₂, hc₂₃] at h₁₂ h₂₃
      case lt.lt =>
        have hc₁₃ : e₁.cmp e₃ = Ordering.lt :=
          cmp_eq_lt_of_lt h₁.fst h₃.fst (lt_trans h₁₂ h₂₃)
        simp only [nadd_oadd_of_lt hc₁₂, nadd_oadd_of_lt hc₂₃,
          nadd_oadd_of_lt hc₁₃]
        apply congrArg (ONote.oadd e₃ n₃)
        simpa only [nadd_oadd_of_lt hc₁₂] using
          nadd_assoc (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₂ n₂ a₂) a₃
            h₁ h₂ h₃.snd
      case lt.eq =>
        obtain rfl := h₂₃
        simp only [nadd_oadd_of_lt hc₁₂, nadd_oadd_of_eq hc₂₃]
        apply congrArg (ONote.oadd e₂ (n₂ + n₃))
        exact nadd_assoc (ONote.oadd e₁ n₁ a₁) a₂ a₃ h₁ h₂.snd h₃.snd
      case lt.gt =>
        simp only [nadd_oadd_of_lt hc₁₂, nadd_oadd_of_gt hc₂₃]
        apply congrArg (ONote.oadd e₂ n₂)
        exact nadd_assoc (ONote.oadd e₁ n₁ a₁) a₂ (ONote.oadd e₃ n₃ a₃)
          h₁ h₂.snd h₃
      case eq.lt =>
        obtain rfl := h₁₂
        simp only [nadd_oadd_of_eq hc₁₂, nadd_oadd_of_lt hc₂₃]
        apply congrArg (ONote.oadd e₃ n₃)
        simpa only [nadd_oadd_of_eq hc₁₂] using
          nadd_assoc (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₁ n₂ a₂) a₃
            h₁ h₂ h₃.snd
      case eq.eq =>
        obtain rfl := h₁₂
        obtain rfl := h₂₃
        simp only [nadd_oadd_of_eq hc₁₂, add_assoc]
        apply congrArg (ONote.oadd e₁ (n₁ + (n₂ + n₃)))
        exact nadd_assoc a₁ a₂ a₃ h₁.snd h₂.snd h₃.snd
      case eq.gt =>
        obtain rfl := h₁₂
        simp only [nadd_oadd_of_eq hc₁₂, nadd_oadd_of_gt hc₂₃]
        apply congrArg (ONote.oadd e₁ (n₁ + n₂))
        exact nadd_assoc a₁ a₂ (ONote.oadd e₃ n₃ a₃) h₁.snd h₂.snd h₃
      case gt.lt =>
        have h₁₃ : ((e₁.cmp e₃).Compares e₁ e₃) :=
          @ONote.cmp_compares _ _ h₁.fst h₃.fst
        cases hc₁₃ : e₁.cmp e₃ <;> simp only [hc₁₃] at h₁₃
        case lt =>
          simp only [nadd_oadd_of_gt hc₁₂, nadd_oadd_of_lt hc₂₃,
            nadd_oadd_of_lt hc₁₃]
          apply congrArg (ONote.oadd e₃ n₃)
          simpa only [nadd_oadd_of_gt hc₁₂] using
            nadd_assoc (ONote.oadd e₁ n₁ a₁) (ONote.oadd e₂ n₂ a₂) a₃
              h₁ h₂ h₃.snd
        case eq =>
          obtain rfl := h₁₃
          simp only [nadd_oadd_of_gt hc₁₂, nadd_oadd_of_lt hc₂₃,
            nadd_oadd_of_eq hc₁₃]
          apply congrArg (ONote.oadd e₁ (n₁ + n₃))
          exact nadd_assoc a₁ (ONote.oadd e₂ n₂ a₂) a₃ h₁.snd h₂ h₃.snd
        case gt =>
          simp only [nadd_oadd_of_gt hc₁₂, nadd_oadd_of_lt hc₂₃,
            nadd_oadd_of_gt hc₁₃]
          apply congrArg (ONote.oadd e₁ n₁)
          simpa only [nadd_oadd_of_lt hc₂₃] using
            nadd_assoc a₁ (ONote.oadd e₂ n₂ a₂) (ONote.oadd e₃ n₃ a₃)
              h₁.snd h₂ h₃
      case gt.eq =>
        obtain rfl := h₂₃
        simp only [nadd_oadd_of_gt hc₁₂, nadd_oadd_of_eq hc₂₃]
        apply congrArg (ONote.oadd e₁ n₁)
        simpa only [nadd_oadd_of_eq hc₂₃] using
          nadd_assoc a₁ (ONote.oadd e₂ n₂ a₂) (ONote.oadd e₂ n₃ a₃)
            h₁.snd h₂ h₃
      case gt.gt =>
        have hc₁₃ : e₁.cmp e₃ = Ordering.gt :=
          cmp_eq_gt_of_gt h₁.fst h₃.fst (lt_trans h₂₃ h₁₂)
        simp only [nadd_oadd_of_gt hc₁₂, nadd_oadd_of_gt hc₂₃,
          nadd_oadd_of_gt hc₁₃]
        apply congrArg (ONote.oadd e₁ n₁)
        simpa only [nadd_oadd_of_gt hc₂₃] using
          nadd_assoc a₁ (ONote.oadd e₂ n₂ a₂) (ONote.oadd e₃ n₃ a₃)
            h₁.snd h₂ h₃
  termination_by a b c => nsize a + nsize b + nsize c
  decreasing_by
    all_goals simp_wf
    all_goals (try simp_all)
    all_goals omega

end OrdinalAnalysis
