import OrdinalAnalysis.KPi.RS.StarBasic

/-!
# The RS calculus, part 7: identification of sentences that differ only in their presentation

B92 works with formulas up to literal identity.  In the de Bruijn presentation of `D0` the same
sentence has several representatives (variables renamed, atoms with permuted environments).
`Sim R A B` says that the junctors of `A` and `B` correspond, member by member, with the same
`k`-data, recursively.  `Star.sim` (the `σ = 0` calculus, i.e. `(⋀)*`, `(⋁)*` only) transports a
derivation along `Sim`:  if every member of `Δ` has a `Sim`-partner in `Δ'`, then `⊢* Δ ⇒ ⊢* Δ'`.
-/

open Ordinal

set_option autoImplicit false

namespace OrdinalAnalysis.KPi.RS

variable {R : Set Ordinal.{1}}

/-- `A` and `B` have corresponding junctors (same kind, same `k`, matching members and `k`-labels). -/
inductive Sim (R : Set Ordinal.{1}) : RSS → RSS → Prop
  | mk {A B : RSS} (hor : (expand R A).isOr = (expand R B).isOr) (hk : A.k = B.k)
      (f : (expand R A).J → (expand R B).J)
      (hf : ∀ j, Sim R ((expand R A).child j) ((expand R B).child (f j)))
      (hfk : ∀ j, (expand R B).ks (f j) = (expand R A).ks j)
      (g : (expand R B).J → (expand R A).J)
      (hg : ∀ j, Sim R ((expand R A).child (g j)) ((expand R B).child j))
      (hgk : ∀ j, (expand R A).ks (g j) = (expand R B).ks j) : Sim R A B

theorem Sim.refl (A : RSS) : Sim R A A := by
  refine rk_ind (P := fun A => Sim R A A) (fun A ih => ?_) A
  exact Sim.mk rfl rfl id (fun j => ih _ (child_rk_lt R A j)) (fun j => rfl)
    id (fun j => ih _ (child_rk_lt R A j)) (fun j => rfl)

theorem Sim.symm {A B : RSS} (h : Sim R A B) : Sim R B A := by
  induction h with
  | mk hor hk f hf hfk g hg hgk ihf ihg =>
    exact Sim.mk hor.symm hk.symm g ihg hgk f ihf hfk

theorem Sim.k_eq {A B : RSS} (h : Sim R A B) : A.k = B.k := by
  cases h with
  | mk hor hk f hf hfk g hg hgk => exact hk

theorem Sim.isOr_eq {A B : RSS} (h : Sim R A B) : (expand R A).isOr = (expand R B).isOr := by
  cases h with
  | mk hor hk f hf hfk g hg hgk => exact hor

theorem Sim.trans {A B C : RSS} (h1 : Sim R A B) (h2 : Sim R B C) : Sim R A C := by
  induction h1 generalizing C with
  | @mk A B hor hk f hf hfk g hg hgk ihf ihg =>
    cases h2 with
    | @mk _ _ hor' hk' f' hf' hfk' g' hg' hgk' =>
      refine Sim.mk (hor.trans hor') (hk.trans hk') (f' ∘ f) (fun j => ihf j (hf' (f j)))
        (fun j => ?_) (g ∘ g') (fun j => ihg (g' j) (hg' j)) (fun j => ?_)
      · show (expand R C).ks (f' (f j)) = (expand R A).ks j
        rw [hfk', hfk]
      · show (expand R A).ks (g (g' j)) = (expand R C).ks j
        rw [hgk, hgk']

/-! ### transport of `⊢*`-derivations along `Sim` -/

theorem Star.sim_aux {σ : Ordinal.{1}} {Δ : Set RSS} (h : Star R σ Δ) :
    σ = 0 → ∀ Δ' : Set RSS, (∀ x ∈ Δ, ∃ y ∈ Δ', Sim R x y) → Star R σ Δ' := by
  induction h with
  | @all A Γ σ hA h ih =>
    intro hσ Δ' hΔ'
    obtain ⟨A', hA'Δ', hs⟩ := hΔ' A (Set.mem_insert _ _)
    have hor := hs.isOr_eq
    cases hs with
    | @mk _ _ hor hk f hf hfk g hg hgk =>
      have hA' : (expand R A').isOr = false := by rw [← hor]; exact hA
      refine Star.all' hA'Δ' hA' (fun j' => ?_)
      refine ih (g j') hσ _ ?_
      intro x hx
      rcases hx with rfl | hx
      · exact ⟨_, Set.mem_insert _ _, hg j'⟩
      · obtain ⟨y, hy, hs⟩ := hΔ' x (Set.mem_insert_of_mem _ hx)
        exact ⟨y, Set.mem_insert_of_mem _ hy, hs⟩
  | @ex A Γ σ js hfin hA hk h ih =>
    intro hσ Δ' hΔ'
    obtain ⟨A', hA'Δ', hs⟩ := hΔ' A (Set.mem_insert _ _)
    cases hs with
    | @mk _ _ hor hk0 f hf hfk g hg hgk =>
      have hA' : (expand R A').isOr = true := by rw [← hor]; exact hA
      have hkS : kSeq (insert A Γ) ⊆ kSeq Δ' := by
        rintro ξ ⟨x, hx, hξ⟩
        obtain ⟨y, hy, hxy⟩ := hΔ' x hx
        exact ⟨y, hy, by rw [← hxy.k_eq]; exact hξ⟩
      refine Star.ex' hA'Δ' (f '' js) (hfin.image f) hA' ?_ ?_
      · rintro j' ⟨j, hj, rfl⟩
        rw [hfk j]
        exact (hk j hj).trans (starK_mono R hkS)
      · refine ih hσ _ ?_
        intro x hx
        rcases hx with hx | ⟨j, hj, rfl⟩
        · obtain ⟨y, hy, hs⟩ := hΔ' x (Set.mem_insert_of_mem _ hx)
          exact ⟨y, Or.inl hy, hs⟩
        · exact ⟨_, Or.inr ⟨f j, ⟨j, hj, rfl⟩, rfl⟩, hf j⟩
  | @ad n i B Γ σ ρ h hr ih =>
    intro hσ
    subst hσ
    exact absurd hr (not_lt_of_ge zero_le)
  | @ref κ S hκ Γ σ hσ0 =>
    intro hσ
    subst hσ
    exact absurd hσ0 (lt_irrefl _)
  | @found α n A ρ Γ σ hσ0 =>
    intro hσ
    subst hσ
    exact absurd hσ0 (lt_irrefl _)

/-- **Replacement** for `⊢*`: if every member of `Δ` has a `Sim`-partner in `Δ'` then `⊢* Δ ⇒ ⊢* Δ'`. -/
theorem Star.sim {Δ Δ' : Set RSS} (h : Star R 0 Δ) (hΔ : ∀ x ∈ Δ, ∃ y ∈ Δ', Sim R x y) :
    Star R 0 Δ' :=
  Star.sim_aux h rfl Δ' hΔ

/-! ### `Sim` for the sentence formers -/

theorem Sim.and {A A' B B' : RSS} (hA : Sim R A A') (hB : Sim R B B') :
    Sim R (RSS.and A B) (RSS.and A' B') := by
  refine Sim.mk rfl (by simp [RSS.k, hA.k_eq, hB.k_eq]) id ?_ (fun j => rfl) id ?_ (fun j => rfl)
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hB
    · exact hA
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hB
    · exact hA

theorem Sim.or {A A' B B' : RSS} (hA : Sim R A A') (hB : Sim R B B') :
    Sim R (RSS.or A B) (RSS.or A' B') := by
  refine Sim.mk rfl (by simp [RSS.k, hA.k_eq, hB.k_eq]) id ?_ (fun j => rfl) id ?_ (fun j => rfl)
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hB
    · exact hA
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hB
    · exact hA

theorem RSS.k_base {n : ℕ} (φ : D0 n) (ρ : Fin n → T) :
    (RSS.base φ ρ).k = kD φ (fun i => (ρ i).k) := rfl

theorem sim_mem_atom {n n' : ℕ} (i j : Fin n) (i' j' : Fin n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hi : ρ i = ρ' i') (hj : ρ j = ρ' j') :
    Sim R (RSS.base (D0.mem i j) ρ) (RSS.base (D0.mem i' j') ρ') := by
  have hk : (RSS.base (D0.mem i j) ρ).k = (RSS.base (D0.mem i' j') ρ').k := by
    simp only [RSS.k_base, kD, hi, hj]
  refine Sim.mk rfl hk (fun t => ⟨t.1, by rw [← hj]; exact t.2⟩) ?_ (fun t => rfl)
    (fun t => ⟨t.1, by rw [hj]; exact t.2⟩) ?_ (fun t => rfl)
  · intro t
    show Sim R (RSS.and (memInst t.1 (ρ j)) (eqS t.1 (ρ i)))
      (RSS.and (memInst t.1 (ρ' j')) (eqS t.1 (ρ' i')))
    rw [← hi, ← hj]
    exact Sim.refl _
  · intro t
    show Sim R (RSS.and (memInst t.1 (ρ j)) (eqS t.1 (ρ i)))
      (RSS.and (memInst t.1 (ρ' j')) (eqS t.1 (ρ' i')))
    rw [hi, hj]
    exact Sim.refl _

theorem sim_nmem_atom {n n' : ℕ} (i j : Fin n) (i' j' : Fin n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hi : ρ i = ρ' i') (hj : ρ j = ρ' j') :
    Sim R (RSS.base (D0.nmem i j) ρ) (RSS.base (D0.nmem i' j') ρ') := by
  have hk : (RSS.base (D0.nmem i j) ρ).k = (RSS.base (D0.nmem i' j') ρ').k := by
    simp only [RSS.k_base, kD, hi, hj]
  refine Sim.mk rfl hk (fun t => ⟨t.1, by rw [← hj]; exact t.2⟩) ?_ (fun t => rfl)
    (fun t => ⟨t.1, by rw [hj]; exact t.2⟩) ?_ (fun t => rfl)
  · intro t
    show Sim R (RSS.or (memInst t.1 (ρ j)).neg (eqS t.1 (ρ i)).neg)
      (RSS.or (memInst t.1 (ρ' j')).neg (eqS t.1 (ρ' i')).neg)
    rw [← hi, ← hj]
    exact Sim.refl _
  · intro t
    show Sim R (RSS.or (memInst t.1 (ρ j)).neg (eqS t.1 (ρ i)).neg)
      (RSS.or (memInst t.1 (ρ' j')).neg (eqS t.1 (ρ' i')).neg)
    rw [hi, hj]
    exact Sim.refl _

theorem sim_ad_atom {n n' : ℕ} (i : Fin n) (i' : Fin n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hi : ρ i = ρ' i') :
    Sim R (RSS.base (D0.ad i) ρ) (RSS.base (D0.ad i') ρ') := by
  have hk : (RSS.base (D0.ad i) ρ).k = (RSS.base (D0.ad i') ρ').k := by
    simp only [RSS.k_base, kD, hi]
  refine Sim.mk rfl hk (fun κ => ⟨κ.1, by rw [← hi]; exact κ.2⟩) ?_ (fun t => rfl)
    (fun κ => ⟨κ.1, by rw [hi]; exact κ.2⟩) ?_ (fun t => rfl)
  · intro κ
    show Sim R (eqS (T.L κ.1) (ρ i)) (eqS (T.L κ.1) (ρ' i'))
    rw [← hi]
    exact Sim.refl _
  · intro κ
    show Sim R (eqS (T.L κ.1) (ρ i)) (eqS (T.L κ.1) (ρ' i'))
    rw [hi]
    exact Sim.refl _

theorem sim_nad_atom {n n' : ℕ} (i : Fin n) (i' : Fin n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hi : ρ i = ρ' i') :
    Sim R (RSS.base (D0.nad i) ρ) (RSS.base (D0.nad i') ρ') := by
  have hk : (RSS.base (D0.nad i) ρ).k = (RSS.base (D0.nad i') ρ').k := by
    simp only [RSS.k_base, kD, hi]
  refine Sim.mk rfl hk (fun κ => ⟨κ.1, by rw [← hi]; exact κ.2⟩) ?_ (fun t => rfl)
    (fun κ => ⟨κ.1, by rw [hi]; exact κ.2⟩) ?_ (fun t => rfl)
  · intro κ
    show Sim R (eqS (T.L κ.1) (ρ i)).neg (eqS (T.L κ.1) (ρ' i')).neg
    rw [← hi]
    exact Sim.refl _
  · intro κ
    show Sim R (eqS (T.L κ.1) (ρ i)).neg (eqS (T.L κ.1) (ρ' i')).neg
    rw [hi]
    exact Sim.refl _

theorem sim_band_gen {n n' : ℕ} (X Y : D0 n) (X' Y' : D0 n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hX : Sim R (RSS.base X ρ) (RSS.base X' ρ')) (hY : Sim R (RSS.base Y ρ) (RSS.base Y' ρ')) :
    Sim R (RSS.base (D0.and X Y) ρ) (RSS.base (D0.and X' Y') ρ') := by
  have hk : (RSS.base (D0.and X Y) ρ).k = (RSS.base (D0.and X' Y') ρ').k := by
    have h1 := hX.k_eq
    have h2 := hY.k_eq
    simp only [RSS.k_base] at h1 h2 ⊢
    simp only [kD]
    rw [h1, h2]
  refine Sim.mk rfl hk id ?_ (fun j => rfl) id ?_ (fun j => rfl)
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hY
    · exact hX
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hY
    · exact hX

theorem sim_bor_gen {n n' : ℕ} (X Y : D0 n) (X' Y' : D0 n') (ρ : Fin n → T) (ρ' : Fin n' → T)
    (hX : Sim R (RSS.base X ρ) (RSS.base X' ρ')) (hY : Sim R (RSS.base Y ρ) (RSS.base Y' ρ')) :
    Sim R (RSS.base (D0.or X Y) ρ) (RSS.base (D0.or X' Y') ρ') := by
  have hk : (RSS.base (D0.or X Y) ρ).k = (RSS.base (D0.or X' Y') ρ').k := by
    have h1 := hX.k_eq
    have h2 := hY.k_eq
    simp only [RSS.k_base] at h1 h2 ⊢
    simp only [kD]
    rw [h1, h2]
  refine Sim.mk rfl hk id ?_ (fun j => rfl) id ?_ (fun j => rfl)
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hY
    · exact hX
  · intro j
    rcases j with ⟨b⟩
    cases b
    · exact hY
    · exact hX

theorem sim_bex_gen {n n' : ℕ} (b : Bd n) (b' : Bd n') (X : D0 (n + 1)) (X' : D0 (n' + 1))
    (ρ : Fin n → T) (ρ' : Fin n' → T) (hb : resBd b ρ = resBd b' ρ')
    (hX : ∀ t : T, Sim R (RSS.base X (ext ρ t)) (RSS.base X' (ext ρ' t)))
    (hk : (RSS.base (D0.bex b X) ρ).k = (RSS.base (D0.bex b' X') ρ').k) :
    Sim R (RSS.base (D0.bex b X) ρ) (RSS.base (D0.bex b' X') ρ') := by
  refine Sim.mk rfl hk (fun t => ⟨t.1, by rw [← hb]; exact t.2⟩) ?_ (fun t => rfl)
    (fun t => ⟨t.1, by rw [hb]; exact t.2⟩) ?_ (fun t => rfl)
  · intro t
    show Sim R (RSS.and (memInst t.1 (resBd b ρ)) (RSS.base X (ext ρ t.1)))
      (RSS.and (memInst t.1 (resBd b' ρ')) (RSS.base X' (ext ρ' t.1)))
    rw [← hb]
    exact Sim.and (Sim.refl _) (hX t.1)
  · intro t
    show Sim R (RSS.and (memInst t.1 (resBd b ρ)) (RSS.base X (ext ρ t.1)))
      (RSS.and (memInst t.1 (resBd b' ρ')) (RSS.base X' (ext ρ' t.1)))
    rw [hb]
    exact Sim.and (Sim.refl _) (hX t.1)

theorem sim_ball_gen {n n' : ℕ} (b : Bd n) (b' : Bd n') (X : D0 (n + 1)) (X' : D0 (n' + 1))
    (ρ : Fin n → T) (ρ' : Fin n' → T) (hb : resBd b ρ = resBd b' ρ')
    (hX : ∀ t : T, Sim R (RSS.base X (ext ρ t)) (RSS.base X' (ext ρ' t)))
    (hk : (RSS.base (D0.ball b X) ρ).k = (RSS.base (D0.ball b' X') ρ').k) :
    Sim R (RSS.base (D0.ball b X) ρ) (RSS.base (D0.ball b' X') ρ') := by
  refine Sim.mk rfl hk (fun t => ⟨t.1, by rw [← hb]; exact t.2⟩) ?_ (fun t => rfl)
    (fun t => ⟨t.1, by rw [hb]; exact t.2⟩) ?_ (fun t => rfl)
  · intro t
    show Sim R (RSS.or (memInst t.1 (resBd b ρ)).neg (RSS.base X (ext ρ t.1)))
      (RSS.or (memInst t.1 (resBd b' ρ')).neg (RSS.base X' (ext ρ' t.1)))
    rw [← hb]
    exact Sim.or (Sim.refl _) (hX t.1)
  · intro t
    show Sim R (RSS.or (memInst t.1 (resBd b ρ)).neg (RSS.base X (ext ρ t.1)))
      (RSS.or (memInst t.1 (resBd b' ρ')).neg (RSS.base X' (ext ρ' t.1)))
    rw [hb]
    exact Sim.or (Sim.refl _) (hX t.1)

theorem resBd_rename_eq {m k k' : ℕ} (b : Bd m) (f : Fin m → Fin k) (f' : Fin m → Fin k')
    (ρ : Fin k → T) (ρ' : Fin k' → T) (h : ∀ i, ρ (f i) = ρ' (f' i)) :
    resBd (b.rename f) ρ = resBd (b.rename f') ρ' := by
  cases b with
  | var i => exact h i
  | lev α => rfl

theorem k_base_rename_eq {m k k' : ℕ} (φ : D0 m) (f : Fin m → Fin k) (f' : Fin m → Fin k')
    (ρ : Fin k → T) (ρ' : Fin k' → T) (h : ∀ i, ρ (f i) = ρ' (f' i)) :
    (RSS.base (φ.rename f) ρ).k = (RSS.base (φ.rename f') ρ').k := by
  simp only [RSS.k_base, kD_rename]
  congr 1
  funext i
  simp [Function.comp, h i]

theorem ext_lift_eq {m k k' : ℕ} (f : Fin m → Fin k) (f' : Fin m → Fin k')
    (ρ : Fin k → T) (ρ' : Fin k' → T) (h : ∀ i, ρ (f i) = ρ' (f' i)) (t : T) :
    ∀ i, (ext ρ t) (liftF f i) = (ext ρ' t) (liftF f' i) := by
  intro i
  induction i using Fin.lastCases with
  | last => simp
  | cast j => simp [h j]

/-- renaming variables and adjusting the environment accordingly does not change the sentence. -/
theorem sim_rename : ∀ {m k k' : ℕ} (φ : D0 m) (f : Fin m → Fin k) (f' : Fin m → Fin k')
    (ρ : Fin k → T) (ρ' : Fin k' → T), (∀ i, ρ (f i) = ρ' (f' i)) →
    Sim R (RSS.base (φ.rename f) ρ) (RSS.base (φ.rename f') ρ') := by
  intro m k k' φ
  induction φ generalizing k k' with
  | mem i j => intro f f' ρ ρ' h; exact sim_mem_atom _ _ _ _ ρ ρ' (h i) (h j)
  | nmem i j => intro f f' ρ ρ' h; exact sim_nmem_atom _ _ _ _ ρ ρ' (h i) (h j)
  | ad i => intro f f' ρ ρ' h; exact sim_ad_atom _ _ ρ ρ' (h i)
  | nad i => intro f f' ρ ρ' h; exact sim_nad_atom _ _ ρ ρ' (h i)
  | and X Y ihX ihY =>
    intro f f' ρ ρ' h
    exact sim_band_gen _ _ _ _ ρ ρ' (ihX f f' ρ ρ' h) (ihY f f' ρ ρ' h)
  | or X Y ihX ihY =>
    intro f f' ρ ρ' h
    exact sim_bor_gen _ _ _ _ ρ ρ' (ihX f f' ρ ρ' h) (ihY f f' ρ ρ' h)
  | bex b X ihX =>
    intro f f' ρ ρ' h
    exact sim_bex_gen _ _ _ _ ρ ρ' (resBd_rename_eq b f f' ρ ρ' h)
      (fun t => ihX (liftF f) (liftF f') _ _ (ext_lift_eq f f' ρ ρ' h t))
      (k_base_rename_eq (D0.bex b X) f f' ρ ρ' h)
  | ball b X ihX =>
    intro f f' ρ ρ' h
    exact sim_ball_gen _ _ _ _ ρ ρ' (resBd_rename_eq b f f' ρ ρ' h)
      (fun t => ihX (liftF f) (liftF f') _ _ (ext_lift_eq f f' ρ ρ' h t))
      (k_base_rename_eq (D0.ball b X) f f' ρ ρ' h)

end OrdinalAnalysis.KPi.RS
