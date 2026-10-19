module

public import OrdinalAnalysis.KPi.RS.StarLemmas

/-!
# The RS calculus, part 9: B92 Lemma 2.5 (reflexivity of `=`, `L_β`-facts)

Ambient style (the principal sentence is in the ambient sequent `Δ`).  Atomic rules are restated
in a form with *equations* `ρ i = s` for the arguments (so that no rewriting inside dependent
environments is needed), see `star_mem'`, `star_nmem'`, `star_ad'`, `star_nad'`, `star_bex'`,
`star_ball'`.

* `star_nmem_irrefl` (2.5 a), `star_eq_refl`, `star_sub_refl` (b), `star_mem_inst` (c),
  `star_neq_symm` (d), `star_mem_L`, `star_memInst_L'` (e), `star_tran_L` (f),
  `star_ex_infinite` (g), `star_ad_L` (h).
-/

@[expose] public section

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}} {σ : Ordinal.{1}}

theorem hk_of_mem {A : RSS} {Δ : Set RSS} {s : Set Ordinal.{1}} (hA : A ∈ Δ) (h : s ⊆ A.k) :
    s ⊆ starK R (kSeq Δ) :=
  (h.trans (k_sub_kSeq hA)).trans (subset_starK R _)

/-- prove `A ∈ Δ` for sets built from `insert`, `∪`, singletons. -/
macro "sub_tac_mem" : tactic =>
  `(tactic| (simp only [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff, true_or, or_true]))

/-! ### the rules with equations for the arguments -/

theorem star_mem' {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {s1 s2 : T}
    (hA : RSS.base (D0.mem i j) ρ ∈ Δ) (h1 : ρ i = s1) (h2 : ρ j = s2) (t : T)
    (ht : t.level < s2.level) (hk : t.k ⊆ starK R (kSeq Δ))
    (hm : Star R σ (insert (memInst t s2) Δ)) (he : Star R σ (insert (eqS t s1) Δ)) :
    Star R σ Δ := by
  subst h1 h2
  exact star_mem_of hA t ht hk hm he

theorem star_nmem' {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {s1 s2 : T}
    (hA : RSS.base (D0.nmem i j) ρ ∈ Δ) (h1 : ρ i = s1) (h2 : ρ j = s2)
    (h : ∀ t : T, t.level < s2.level →
      Star R σ (insert (memInst t s2).neg (insert (eqS t s1).neg Δ))) : Star R σ Δ := by
  subst h1 h2
  exact star_nmem_of hA h

theorem star_ad' {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {s : T}
    (hA : RSS.base (D0.ad i) ρ ∈ Δ) (h1 : ρ i = s) (κ : Ordinal.{1}) (hκ : κ ∈ R) (hκ0 : 0 < κ)
    (hle : κ ≤ s.level) (hk : ({κ} : Set Ordinal.{1}) ⊆ starK R (kSeq Δ))
    (h : Star R σ (insert (eqS (T.L κ) s) Δ)) : Star R σ Δ := by
  subst h1
  exact star_ad_of hA κ hκ hκ0 hle hk h

theorem star_nad' {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {s : T}
    (hA : RSS.base (D0.nad i) ρ ∈ Δ) (h1 : ρ i = s)
    (h : ∀ κ : Ordinal.{1}, κ ∈ R → 0 < κ → κ ≤ s.level →
      Star R σ (insert (eqS (T.L κ) s).neg Δ)) : Star R σ Δ := by
  subst h1
  exact star_nad_of hA h

theorem star_bex' {n : ℕ} {b : Bd n} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS} {s : T}
    (hA : RSS.base (D0.bex b X) ρ ∈ Δ) (hb : resBd b ρ = s) (t : T) (ht : t.level < s.level)
    (hk : t.k ⊆ starK R (kSeq Δ))
    (h1 : Star R σ (insert (memInst t s) Δ))
    (h2 : Star R σ (insert (RSS.base X (ext ρ t)) Δ)) : Star R σ Δ := by
  subst hb
  exact star_bex_of hA t ht hk h1 h2

theorem star_ball' {n : ℕ} {b : Bd n} {X : D0 (n + 1)} {ρ : Fin n → T} {Δ : Set RSS} {s : T}
    (hA : RSS.base (D0.ball b X) ρ ∈ Δ) (hb : resBd b ρ = s)
    (h : ∀ t : T, t.level < s.level →
      Star R σ (insert (memInst t s).neg (insert (RSS.base X (ext ρ t)) Δ))) : Star R σ Δ := by
  subst hb
  exact star_ball_of hA h

/-! ### (a), (b) -/

theorem k_neg_memInst (t b : T) : t.k ⊆ (memInst t b).neg.k := by
  rw [RSS.k_neg]
  exact k_memInst t b

/-- the `[b ⊆ a]`-style sentence `∀x∈ρ i (x ∈ ρ j)` is derivable once all `t ∈ T_{|a|}` are
self-equal. -/
theorem star_sub_refl_aux {a : T}
    (ih : ∀ t : T, t.level < a.level → ∀ Δ : Set RSS, eqS t t ∈ Δ → Star R σ Δ)
    {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS} (hi : ρ i = a) (hj : ρ j = a)
    (hA : RSS.base (D0.subset i j) ρ ∈ Δ) : Star R σ Δ := by
  refine star_ball' hA hi (fun t ht => ?_)
  have hmem : RSS.base (D0.mem (Fin.last n) j.castSucc) (ext ρ t) ∈
      insert (memInst t a).neg (insert (RSS.base (D0.mem (Fin.last n) j.castSucc) (ext ρ t)) Δ) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  refine star_mem' (s1 := t) (s2 := a) hmem (by simp) (by simpa using hj) t ht
    (hk_of_mem (Set.mem_insert _ _) (k_neg_memInst t a)) ?_ ?_
  · exact star_tnd' (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact ih t ht _ (Set.mem_insert _ _)

theorem star_eq_refl_aux : ∀ a : T, ∀ Δ : Set RSS, eqS a a ∈ Δ → Star R σ Δ := by
  intro a
  refine (InvImage.wf T.rk Ordinal.lt_wf).induction
    (C := fun a => ∀ Δ : Set RSS, eqS a a ∈ Δ → Star R σ Δ) a (fun a ih => ?_)
  intro Δ hΔ
  have ih' : ∀ t : T, t.level < a.level → ∀ Δ : Set RSS, eqS t t ∈ Δ → Star R σ Δ :=
    fun t ht => ih t (show t.rk < a.rk by simpa using T.rk_add_lt ht 0)
  refine star_band_of (n := 2) (X := D0.subset 0 1) (Y := D0.subset 1 0) (ρ := ![a, a]) hΔ ?_ ?_
  · exact star_sub_refl_aux ih' (i := 0) (j := 1) rfl rfl (Set.mem_insert _ _)
  · exact star_sub_refl_aux ih' (i := 1) (j := 0) rfl rfl (Set.mem_insert _ _)

/-- `⊢* a = a` (B92 2.5 b). -/
theorem star_eq_refl {a : T} {Δ : Set RSS} (h : eqS a a ∈ Δ) : Star R σ Δ :=
  star_eq_refl_aux a Δ h

/-- `⊢* a ⊆ a`, for any presentation. -/
theorem star_sub_refl {a : T} {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hi : ρ i = a) (hj : ρ j = a) (hA : RSS.base (D0.subset i j) ρ ∈ Δ) : Star R σ Δ :=
  star_sub_refl_aux (fun t _ Δ' h => star_eq_refl_aux t Δ' h) hi hj hA

/-- `⊢* b ∉ b` (B92 2.5 a). -/
theorem star_nmem_irrefl_aux : ∀ b : T, ∀ {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS},
    ρ i = b → ρ j = b → RSS.base (D0.nmem i j) ρ ∈ Δ → Star R σ Δ := by
  intro b
  refine (InvImage.wf T.rk Ordinal.lt_wf).induction
    (C := fun b => ∀ {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS},
      ρ i = b → ρ j = b → RSS.base (D0.nmem i j) ρ ∈ Δ → Star R σ Δ) b (fun b ih => ?_)
  intro n i j ρ Δ hi hj hA
  refine star_nmem' hA hi hj (fun t ht => ?_)
  have hne : (eqS t b).neg ∈ insert (memInst t b).neg (insert (eqS t b).neg Δ) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  refine star_neq_of hne ?_
  have hN2 : Nq2 t b ∈ insert (Nq1 t b) (insert (Nq2 t b)
      (insert (memInst t b).neg (insert (eqS t b).neg Δ))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  refine star_bex' (b := Bd.var 1) (X := D0.nmem (Fin.last 2) (Fin.castSucc 0)) (ρ := ![t, b])
    (s := b) hN2 rfl t ht
    (hk_of_mem (A := (memInst t b).neg) (by simp) (k_neg_memInst t b)) ?_ ?_
  · exact star_tnd' (A := memInst t b) (by simp) (by simp)
  · refine ih t (show t.rk < b.rk by simpa using T.rk_add_lt ht 0) (n := 3)
      (i := Fin.last 2) (j := Fin.castSucc 0) (ρ := ext ![t, b] t) (by simp) (by simp)
      (Set.mem_insert _ _)

theorem star_nmem_irrefl {b : T} {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hi : ρ i = b) (hj : ρ j = b) (hA : RSS.base (D0.nmem i j) ρ ∈ Δ) : Star R σ Δ :=
  star_nmem_irrefl_aux b hi hj hA

/-! ### (c), (e) -/

/-- `⊢* b ∉° a, b ∈ a` for `|b| < |a|` (B92 2.5 c). -/
theorem star_mem_inst {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hA : RSS.base (D0.mem i j) ρ ∈ Δ) (hn : (memInst (ρ i) (ρ j)).neg ∈ Δ)
    (hlt : (ρ i).level < (ρ j).level) : Star R σ Δ :=
  star_mem' hA rfl rfl (ρ i) hlt (hk_of_mem hn (k_neg_memInst _ _))
    (star_tnd' (Set.mem_insert _ _) (Set.mem_insert_of_mem _ hn))
    (star_eq_refl (Set.mem_insert _ _))

/-- `⊢* a ∈ L_β` for `|a| < β` (B92 2.5 e). -/
theorem star_mem_L {n : ℕ} {i j : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {β : Ordinal.{1}}
    (hA : RSS.base (D0.mem i j) ρ ∈ Δ) (hj : ρ j = T.L β) (hi : (ρ i).level < β) :
    Star R σ Δ := by
  have hlt : (ρ i).level < (ρ j).level := by rw [hj]; exact hi
  refine star_mem' hA rfl rfl (ρ i) hlt
    (hk_of_mem hA (by exact Set.subset_union_left)) ?_ (star_eq_refl (Set.mem_insert _ _))
  rw [hj]
  exact star_memInst_L' _ _

/-! ### (d) -/

/-- `⊢* a ≠ b, b = a` (B92 2.5 d), at `σ = 0`. -/
theorem star_neq_symm_zero {a b : T} {Δ : Set RSS} (h1 : Nq1 a b ∈ Δ) (h2 : Nq2 a b ∈ Δ)
    (h : eqS b a ∈ Δ) : Star R 0 Δ := by
  refine star_band_of (n := 2) (X := D0.subset 0 1) (Y := D0.subset 1 0) (ρ := ![b, a]) h ?_ ?_
  · refine Star.sim (star_tnd 0 (RSS.base (D0.subset 0 1) ![b, a])) ?_
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨Nq2 a b, Set.mem_insert_of_mem _ h2, (sim_Nq2 a b).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩
  · refine Star.sim (star_tnd 0 (RSS.base (D0.subset 1 0) ![b, a])) ?_
    intro x hx
    rcases hx with rfl | hx
    · exact ⟨Nq1 a b, Set.mem_insert_of_mem _ h1, (sim_Nq1 a b).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨_, Set.mem_insert _ _, Sim.refl _⟩

theorem star_neq_symm {a b : T} {Δ : Set RSS} (h1 : Nq1 a b ∈ Δ) (h2 : Nq2 a b ∈ Δ)
    (h : eqS b a ∈ Δ) : Star R σ Δ :=
  Star.mono_sigma (star_neq_symm_zero h1 h2 h) zero_le

/-! ### (f), (g): `tran` and `infinite` -/

/-- `tran(x_i) := ∀y∈x ∀z∈y (z ∈ x)`. -/
def D0.tran {n : ℕ} (i : Fin n) : D0 n :=
  .ball (.var i) (.ball (.var (Fin.last n))
    (.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i))))

/-- `infinite(x_i) := ∃x∈u (x ⊆ x) ∧ ∀x∈u ∃y∈u (x ∈ y)` (as printed in B92 p.3). -/
def D0.infinite {n : ℕ} (i : Fin n) : D0 n :=
  .and (.bex (.var i) (D0.subset (Fin.last n) (Fin.last n)))
    (.ball (.var i) (.bex (.var (Fin.castSucc i))
      (.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))))

/-- `⊢* tran(L_α)` (B92 2.5 f). -/
theorem star_tran_L {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {α : Ordinal.{1}}
    (hi : ρ i = T.L α) (hA : RSS.base (D0.tran i) ρ ∈ Δ) : Star R σ Δ := by
  refine star_ball' hA hi (fun t ht => ?_)
  have hB : RSS.base (D0.ball (Bd.var (Fin.last n))
      (D0.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i)))) (ext ρ t) ∈
      insert (memInst t (T.L α)).neg (insert (RSS.base (D0.ball (Bd.var (Fin.last n))
      (D0.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i)))) (ext ρ t)) Δ) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  refine star_ball' hB (s := t) (by simp [resBd]) (fun s hs => ?_)
  have hsα : s.level < α := lt_trans hs ht
  have hM : RSS.base (D0.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i)))
      (ext (ext ρ t) s) ∈ insert (memInst s t).neg (insert (RSS.base
      (D0.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i))) (ext (ext ρ t) s))
      (insert (memInst t (T.L α)).neg (insert (RSS.base (D0.ball (Bd.var (Fin.last n))
      (D0.mem (Fin.last (n + 1)) (Fin.castSucc (Fin.castSucc i)))) (ext ρ t)) Δ))) :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  refine star_mem_L (β := α) hM (by simp [hi]) ?_
  simpa using hsα

/-- `⊢* infinite(L_ω)`, in context: the sequent must already contain `0` among the `k`-data
(this is the case in every use, since the `L_0`-sentences `t ∈° L_β` carry `0`). -/
theorem star_infinite_L {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS}
    (hi : ρ i = T.L ω) (h0 : (0 : Ordinal.{1}) ∈ starK R (kSeq Δ))
    (hA : RSS.base (D0.infinite i) ρ ∈ Δ) : Star R σ Δ := by
  refine star_band_of (n := n) (X := D0.bex (Bd.var i) (D0.subset (Fin.last n) (Fin.last n)))
    (Y := D0.ball (Bd.var i) (D0.bex (Bd.var (Fin.castSucc i))
      (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))))) hA ?_ ?_
  · -- `∃x∈L_ω (x ⊆ x)`, witness `L_0`
    have hX : RSS.base (D0.bex (Bd.var i) (D0.subset (Fin.last n) (Fin.last n))) ρ ∈
        insert (RSS.base (D0.bex (Bd.var i) (D0.subset (Fin.last n) (Fin.last n))) ρ) Δ :=
      Set.mem_insert _ _
    have h0' : (0 : Ordinal.{1}) ∈ starK R (kSeq (insert (RSS.base (D0.bex (Bd.var i)
        (D0.subset (Fin.last n) (Fin.last n))) ρ) Δ)) :=
      starK_mono R (kSeq_mono (Set.subset_insert _ _)) h0
    refine star_bex' hX (s := T.L ω) hi (T.L 0) ?_ ?_ (star_memInst_L' _ _) ?_
    · show (0 : Ordinal.{1}) < ω
      exact omega0_pos
    · intro ξ hξ
      have : ξ = 0 := hξ
      rw [this]; exact h0'
    · exact star_sub_refl (a := T.L 0) (by simp) (by simp) (Set.mem_insert _ _)
  · -- `∀x∈L_ω ∃y∈L_ω (x ∈ y)`
    have hY : RSS.base (D0.ball (Bd.var i) (D0.bex (Bd.var (Fin.castSucc i))
        (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))))) ρ ∈
        insert (RSS.base (D0.ball (Bd.var i) (D0.bex (Bd.var (Fin.castSucc i))
        (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))))) ρ) Δ := Set.mem_insert _ _
    refine star_ball' hY hi (fun b hb => ?_)
    set Δ1 := insert (memInst b (T.L ω)).neg (insert (RSS.base (D0.bex (Bd.var (Fin.castSucc i))
      (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))) (ext ρ b))
      (insert (RSS.base (D0.ball (Bd.var i) (D0.bex (Bd.var (Fin.castSucc i))
        (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1))))) ρ) Δ)) with hΔ1
    have hbω : b.level < ω := hb
    have hsucc : b.level + 1 < ω := by
      have := Ordinal.isSuccLimit_omega0.succ_lt hbω
      simpa using this
    have hbx : RSS.base (D0.bex (Bd.var (Fin.castSucc i))
        (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))) (ext ρ b) ∈ Δ1 :=
      Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    refine star_bex' hbx (s := T.L ω) (by simp [resBd, hi]) (T.L (b.level + 1)) hsucc ?_
      (star_memInst_L' _ _) ?_
    · intro ξ hξ
      have : ξ = b.level + 1 := hξ
      rw [this]
      refine Or.inl (Or.inr ⟨b.level, ?_, rfl⟩)
      exact ⟨(memInst b (T.L ω)).neg, Set.mem_insert _ _, k_neg_memInst b _ (PT.level_mem_k b.1)⟩
    · have hmm : RSS.base (D0.mem (Fin.castSucc (Fin.last n)) (Fin.last (n + 1)))
          (ext (ext ρ b) (T.L (b.level + 1))) ∈ insert (RSS.base (D0.mem (Fin.castSucc (Fin.last n))
          (Fin.last (n + 1))) (ext (ext ρ b) (T.L (b.level + 1)))) Δ1 := Set.mem_insert _ _
      refine star_mem_L (β := b.level + 1) hmm (by simp) ?_
      simp

/-- `⊢* ∃x∈L_α infinite(x)` for `α > ω` (B92 2.5 g), in context (`0` among the `k`-data). -/
theorem star_ex_infinite {n : ℕ} {α : Ordinal.{1}} (hα : ω < α) {ρ : Fin n → T} {Δ : Set RSS}
    (h0 : (0 : Ordinal.{1}) ∈ starK R (kSeq Δ))
    (hA : RSS.base (D0.bex (Bd.lev α) (D0.infinite (Fin.last n))) ρ ∈ Δ) : Star R σ Δ := by
  refine star_bex' hA (s := T.L α) rfl (T.L ω) hα ?_ (star_memInst_L' _ _) ?_
  · exact fun ξ hξ => Or.inl (Or.inl (Or.inr hξ))
  · exact star_infinite_L (by simp) (starK_mono R (kSeq_mono (Set.subset_insert _ _)) h0)
      (Set.mem_insert _ _)

/-! ### (h) -/

/-- `⊢* Ad(L_κ)` for `κ ∈ R` (B92 2.5 h). -/
theorem star_ad_L {n : ℕ} {i : Fin n} {ρ : Fin n → T} {Δ : Set RSS} {κ : Ordinal.{1}}
    (hi : ρ i = T.L κ) (hκ : κ ∈ R) (hκ0 : 0 < κ) (hA : RSS.base (D0.ad i) ρ ∈ Δ) :
    Star R σ Δ := by
  refine star_ad' hA hi κ hκ hκ0 (by simp [T.L, T.level, PT.level]) ?_ (star_eq_refl (Set.mem_insert _ _))
  refine hk_of_mem hA ?_
  intro ξ hξ
  have : ξ = κ := hξ
  show ξ ∈ (ρ i).k
  rw [hi, this]
  simp [T.k, PT.k, T.L]

end OrdinalAnalysis.KPi.RS
