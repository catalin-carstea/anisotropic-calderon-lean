import Calderon.CollaboratorLocalJetsSobOct17

/-! Sobolev operators for `LocalJets` (Lassas–Liimatainen–Salo, Prop. A.5): smooth functions in
`W^{k,2}(B)` with bounds, the perturbation operator `w ↦ div(M ∇w)`, and the
constant-coefficient a priori bound. -/

set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open MeasureTheory TopologicalSpace Metric Set
open scoped InnerProductSpace ContDiff Distributions Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.Regularity.Jets
open TauCeti TauCeti.PDE EnergyBridge

/-! ### Cutoff, smooth functions in `W^{k,2}(B)`, and the perturbation operator -/

/-- The fixed cutoff, equal to one on `closedBall 0 1` and supported in `closedBall 0 2`. -/
def cutB : ContDiffBump (0 : R3) := ⟨1, 2, one_pos, one_lt_two⟩

theorem cutB_eq_one {x : R3} (hx : x ∈ closedBall (0 : R3) 1) : cutB x = 1 :=
  cutB.one_of_mem_closedBall hx

theorem cutB_tsupport : tsupport (cutB : R3 → ℝ) = closedBall (0 : R3) 2 := cutB.tsupport_eq

theorem contDiff_cutB : ContDiff ℝ ∞ (cutB : R3 → ℝ) := cutB.contDiff (n := ⊤)

theorem cut_bound (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ g : R3 → ℝ, ContDiff ℝ ∞ g → ∀ δ : ℝ, 0 ≤ δ →
    (∀ j ≤ n, ∀ y ∈ closedBall (0 : R3) 2, ‖iteratedFDeriv ℝ j g y‖ ≤ δ) →
    ∀ j ≤ n, ∀ y, ‖iteratedFDeriv ℝ j (fun y => cutB y * g y) y‖ ≤ C * δ := by
  obtain ⟨Mχ, hMχ, hχ⟩ := HO.exists_iteratedFDeriv_bound contDiff_cutB
    cutB.hasCompactSupport n
  refine ⟨2 ^ n * Mχ, by positivity, fun g hg δ hδ hgb j hj y => ?_⟩
  by_cases hy : y ∈ closedBall (0 : R3) 2
  · refine (norm_iteratedFDeriv_mul_le contDiff_cutB hg y
      (by exact_mod_cast le_top)).trans ?_
    calc ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (cutB : R3 → ℝ) y‖ *
          ‖iteratedFDeriv ℝ (j - i) g y‖
        ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * Mχ * δ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
          gcongr
          · exact hχ i (hi'.trans hj) y
          · exact hgb (j - i) (by omega) y hy
      _ = 2 ^ j * Mχ * δ := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          congr 2
          exact_mod_cast Nat.sum_range_choose j
      _ ≤ 2 ^ n * Mχ * δ := by
          gcongr
          · norm_num
      _ = _ := by ring
  · have hnot : y ∉ tsupport (fun y => cutB y * g y) := by
      intro hmem
      have := (tsupport_mul_subset_left (f := (cutB : R3 → ℝ)) (g := g)) hmem
      rw [cutB_tsupport] at this
      exact hy this
    have : iteratedFDeriv ℝ j (fun y => cutB y * g y) y = 0 := by
      by_contra hne
      exact hnot (support_iteratedFDeriv_subset j hne)
    rw [this, norm_zero]
    positivity

/-- The constant function one on `B`, in `W^{s,2}(B)`. -/
def cutTest : 𝓓((⊤ : Opens R3), ℝ) :=
  ⟨fun y => cutB y, cutB.contDiff, cutB.hasCompactSupport, fun _ _ => trivial⟩

def oneW (s : ℕ) : Wkp (volume : Measure R3) ballOpens 2 s :=
  Wkp.restrictL (le_top : ballOpens ≤ ⊤) s (Wkp.ofTestFunctionₗ (mu := volume) (p := 2) s cutTest)

theorem value_oneW (s : ℕ) :
    ⇑(Wkp.value s (oneW s)) =ᵐ[(volume : Measure R3).restrict ballOpens] fun _ => (1 : ℝ) := by
  have h1 := Wkp.value_restrictL_ae (le_top : ballOpens ≤ ⊤) s
    (Wkp.ofTestFunctionₗ (mu := (volume : Measure R3)) (p := 2) s cutTest)
  have h2 := ae_restrict_of_ae_restrict_of_subset (Set.subset_univ (ballOpens : Set R3))
    (testFunctionLp_apply_ae (mu := (volume : Measure R3)) (Omega := ⊤) 2 cutTest)
  filter_upwards [h1, h2, ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx1 hx2 hx3
  unfold oneW
  rw [hx1, Wkp.value_ofTestFunctionₗ, hx2]
  exact cutB_eq_one (ball_subset_closedBall (by simpa [B] using hx3))

theorem exists_mul_smooth (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ φ : R3 → ℝ, ContDiff ℝ ∞ φ →
    HasCompactSupport φ → ∀ M : ℝ, 0 ≤ M →
    (∀ j : ℕ, j ≤ s + 1 → ∀ x : R3, ‖iteratedFDeriv ℝ j φ x‖ ≤ M) →
    ∃ f : Wkp (volume : Measure R3) ballOpens 2 s,
      ⇑(Wkp.value s f) =ᵐ[(volume : Measure R3).restrict ballOpens] φ ∧ ‖f‖ ≤ C * M := by
  obtain ⟨C, hC0, hC⟩ := DirichletFamily.mulAt (Ω := ballOpens) s
  refine ⟨C * ‖oneW s‖, by positivity, fun φ hφ hc M hM hb => ?_⟩
  obtain ⟨T, hT, hTn⟩ := hC φ hφ hc M hM hb
  refine ⟨T (oneW s), ?_, ?_⟩
  · filter_upwards [hT (oneW s), value_oneW s] with x h1 h2
    rw [h1, h2, mul_one]
  · calc ‖T (oneW s)‖ ≤ ‖T‖ * ‖oneW s‖ := T.le_opNorm _
      _ ≤ C * M * ‖oneW s‖ := by gcongr
      _ = _ := by ring

theorem cutB_mul_ae (g : R3 → ℝ) :
    (fun y => cutB y * g y) =ᵐ[(volume : Measure R3).restrict ballOpens] g := by
  filter_upwards [ae_restrict_mem ballOpens.isOpen.measurableSet] with x hx
  rw [cutB_eq_one (ball_subset_closedBall (by simpa [B] using hx)), one_mul]

theorem exists_wkp_of_contDiff (s : ℕ) {g : R3 → ℝ} (hg : ContDiff ℝ ∞ g) :
    ∃ f : Wkp (volume : Measure R3) ballOpens 2 s,
      ⇑(Wkp.value s f) =ᵐ[(volume : Measure R3).restrict ballOpens] g := by
  obtain ⟨C, -, hC⟩ := exists_mul_smooth s
  have hφ : ContDiff ℝ ∞ (fun y => cutB y * g y) := contDiff_cutB.mul hg
  have hc : HasCompactSupport (fun y => cutB y * g y) := cutB.hasCompactSupport.mul_right
  obtain ⟨M, hM, hb⟩ := HO.exists_iteratedFDeriv_bound hφ hc (s + 1)
  obtain ⟨f, hf, -⟩ := hC _ hφ hc M hM hb
  exact ⟨f, hf.trans (cutB_mul_ae g)⟩

theorem exists_wkp3_bound : ∃ CF : ℝ, 0 ≤ CF ∧ ∀ g : R3 → ℝ, ContDiff ℝ ∞ g → ∀ δ : ℝ, 0 ≤ δ →
    (∀ j ≤ 4, ∀ y ∈ closedBall (0 : R3) 2, ‖iteratedFDeriv ℝ j g y‖ ≤ δ) →
    ∃ f : Wkp (volume : Measure R3) ballOpens 2 3,
      ⇑(Wkp.value 3 f) =ᵐ[(volume : Measure R3).restrict ballOpens] g ∧ ‖f‖ ≤ CF * δ := by
  obtain ⟨Cc, hCc, hcut⟩ := cut_bound 4
  obtain ⟨Cm, hCm, hC⟩ := exists_mul_smooth 3
  refine ⟨Cm * Cc, by positivity, fun g hg δ hδ hgb => ?_⟩
  have hφ : ContDiff ℝ ∞ (fun y => cutB y * g y) := contDiff_cutB.mul hg
  have hc : HasCompactSupport (fun y => cutB y * g y) := cutB.hasCompactSupport.mul_right
  obtain ⟨f, hf, hfn⟩ := hC _ hφ hc (Cc * δ) (by positivity)
    (fun j hj x => hcut g hg δ hδ hgb j hj x)
  exact ⟨f, hf.trans (cutB_mul_ae g), hfn.trans (le_of_eq (by ring))⟩
theorem ibp_w1p (G : W1p (volume : Measure R3) ballOpens 2) (φ : 𝓓(ballOpens, ℝ)) (i : Fin 3) :
    ∫ x in (ballOpens : Set R3), fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
        W1p.value G x = -∫ x in (ballOpens : Set R3), W1p.gradient G x i * φ x := by
  have h := DiffEq.TF.ibp (DiffEq.TF.of φ) (DiffEq.coordDeriv (W1p.hasWeakFDerivOn G) i)
  have hd := (DiffEq.TF.of φ).deriv i
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [show fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) = DiffEq.pd φ i x from rfl,
        hd.zero_of_notMem hx, zero_mul]),
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [(DiffEq.TF.of φ).zero_of_notMem hx, mul_zero])]
  have e1 : (fun x => W1p.gradient G x i * φ x) = fun x => φ x * W1p.gradient G x i := by
    funext x; ring
  rw [e1, h, neg_neg]
  rfl

theorem integral_lp_test (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), F x * φ x =
      ⟪testFunctionLp (mu := (volume : Measure R3)) 2 φ, F⟫_ℝ := by
  rw [← Regularity.integral_mul_eq_inner]
  refine integral_congr_ae ?_
  filter_upwards [testFunctionLp_apply_ae (mu := (volume : Measure R3)) 2 φ] with x hx
  rw [hx]

theorem integrable_lp_test (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (φ : 𝓓(ballOpens, ℝ)) :
    Integrable (fun x => F x * φ x) ((volume : Measure R3).restrict ballOpens) :=
  HO.integrable_mul_test (HO.aeIn_of_mem (HO.mem_Hs_zero F)) φ

theorem integrable_lp_dtest (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens))
    (φ : 𝓓(ballOpens, ℝ)) (i : Fin 3) :
    Integrable (fun x => fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) * F x)
      ((volume : Measure R3).restrict ballOpens) := by
  obtain ⟨ψ, hψ⟩ := (DiffEq.TF.of φ).deriv i
  have := integrable_lp_test F ψ
  refine this.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [hψ]
  rw [mul_comm]
  rfl

section Generic
variable {E G H F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G]
  [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `∑ᵢ ∑ₖ aᵢ ∘ Tᵢₖ ∘ bₖ`. -/
def sumComp (a : Fin 3 → (H →L[ℝ] F)) (T : Fin 3 → Fin 3 → (G →L[ℝ] H))
    (b : Fin 3 → (E →L[ℝ] G)) : E →L[ℝ] F :=
  ∑ i : Fin 3, ∑ k : Fin 3, (a i).comp ((T i k).comp (b k))

theorem norm_sum_comp_le (a : Fin 3 → (H →L[ℝ] F)) (T : Fin 3 → Fin 3 → (G →L[ℝ] H))
    (b : Fin 3 → (E →L[ℝ] G)) {c : ℝ} (hT : ∀ i k, ‖T i k‖ ≤ c) :
    ‖sumComp a T b‖ ≤
      c * ∑ i : Fin 3, ∑ k : Fin 3, ‖a i‖ * ‖b k‖ := by
  unfold sumComp
  calc _ ≤ ∑ i : Fin 3, ‖∑ k : Fin 3, (a i).comp ((T i k).comp (b k))‖ := norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, ‖(a i).comp ((T i k).comp (b k))‖ :=
          Finset.sum_le_sum fun i _ => norm_sum_le _ _
      _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, ‖a i‖ * (c * ‖b k‖) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
          gcongr
          exact hT i k
      _ = _ := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring

theorem apply_sum_comp (L : F →L[ℝ] V) (a : Fin 3 → (H →L[ℝ] F))
    (T : Fin 3 → Fin 3 → (G →L[ℝ] H)) (b : Fin 3 → (E →L[ℝ] G)) (W : E) :
    L (sumComp a T b W) = ∑ i : Fin 3, ∑ k : Fin 3, L (a i (T i k (b k W))) := by
  simp [sumComp, map_sum]

end Generic

section
variable {Ω : Opens R3}

/-- `∂ᵢ : W^{4,2} → W^{3,2}`. -/
def dL3 (i : Fin 3) : Wkp (volume : Measure R3) Ω 2 4 →L[ℝ] Wkp (volume : Measure R3) Ω 2 3 :=
  WkpCalculus.dL i 3

/-- `∂ᵢ : W^{5,2} → W^{4,2}`. -/
def dL4 (i : Fin 3) : Wkp (volume : Measure R3) Ω 2 5 →L[ℝ] Wkp (volume : Measure R3) Ω 2 4 :=
  WkpCalculus.dL i 4

/-- The perturbation operator built from multiplication operators. -/
def pertOp (T : Fin 3 → Fin 3 →
    (Wkp (volume : Measure R3) Ω 2 4 →L[ℝ] Wkp (volume : Measure R3) Ω 2 4)) :
    Wkp (volume : Measure R3) Ω 2 5 →L[ℝ] Wkp (volume : Measure R3) Ω 2 3 :=
  sumComp dL3 T dL4

end

theorem pert_term (M : R3 → Matrix (Fin 3) (Fin 3) ℝ) (W : Wkp (volume : Measure R3) ballOpens 2 5)
    (i k : Fin 3)
    (T : Wkp (volume : Measure R3) ballOpens 2 4 →L[ℝ] Wkp (volume : Measure R3) ballOpens 2 4)
    (hT : ∀ f, ⇑(Wkp.value 4 (T f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => (cutB x * M x i k) * Wkp.value 4 f x) :
    (fun x => M x i k * W1p.gradient (Wkp.firstOrder 4 W) x k) =ᵐ[(volume : Measure R3).restrict ballOpens]
      ⇑(W1p.value (Wkp.firstOrder 3 (T (dL4 k W)))) := by
  rw [Wkp.value_firstOrder]
  filter_upwards [hT (dL4 k W), WkpCalculus.value_d k 4 W, cutB_mul_ae (fun x => M x i k)]
    with x h1 h2 h3
  rw [h1]
  rw [show dL4 (Ω := ballOpens) k W = WkpCalculus.d k 4 W from rfl, h2]
  rw [h3]

theorem pert_term_int (M : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (W : Wkp (volume : Measure R3) ballOpens 2 5) (φ : 𝓓(ballOpens, ℝ)) (i k : Fin 3)
    (T : Wkp (volume : Measure R3) ballOpens 2 4 →L[ℝ] Wkp (volume : Measure R3) ballOpens 2 4)
    (hT : ∀ f, ⇑(Wkp.value 4 (T f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => (cutB x * M x i k) * Wkp.value 4 f x) :
    Integrable (fun x => fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
      (M x i k * W1p.gradient (Wkp.firstOrder 4 W) x k))
      ((volume : Measure R3).restrict ballOpens) ∧
    ∫ x in (ballOpens : Set R3), fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
      (M x i k * W1p.gradient (Wkp.firstOrder 4 W) x k) =
      -∫ x in (ballOpens : Set R3),
        Wkp.value 3 (dL3 i (T (dL4 k W))) x * φ x := by
  have hae := pert_term M W i k T hT
  have hae' : (fun x => fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
      (M x i k * W1p.gradient (Wkp.firstOrder 4 W) x k)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
        W1p.value (Wkp.firstOrder 3 (T (dL4 k W))) x := by
    filter_upwards [hae] with x hx
    rw [hx]
  refine ⟨(integrable_lp_dtest _ φ i).congr hae'.symm, ?_⟩
  rw [integral_congr_ae hae', ibp_w1p]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [WkpCalculus.value_d i 3 (T (dL4 k W))] with x hx
  exact congrArg (fun t => t * φ x) hx.symm

section
variable {Ω : Opens R3}

def derivativeNormSum (Ω : Opens R3) : ℝ :=
  ∑ i : Fin 3, ∑ k : Fin 3, ‖dL3 (Ω := Ω) i‖ * ‖dL4 (Ω := Ω) k‖

theorem derivativeNormSum_nonneg : 0 ≤ derivativeNormSum Ω :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => by positivity

theorem norm_pertOp_le (T : Fin 3 → Fin 3 →
    (Wkp (volume : Measure R3) Ω 2 4 →L[ℝ] Wkp (volume : Measure R3) Ω 2 4)) {c : ℝ}
    (hTn : ∀ i k, ‖T i k‖ ≤ c) : ‖pertOp T‖ ≤ c * derivativeNormSum Ω :=
  norm_sum_comp_le dL3 T dL4 hTn

end

theorem apply_sum_comp_scalar {E G H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : F →L[ℝ] ℝ) (a : Fin 3 → (H →L[ℝ] F))
    (T : Fin 3 → Fin 3 → (G →L[ℝ] H)) (b : Fin 3 → (E →L[ℝ] G)) (W : E) :
    L (sumComp a T b W) = ∑ i : Fin 3, ∑ k : Fin 3, L (a i (T i k (b k W))) := by
  simp [sumComp, map_sum]

theorem inner_value_pertOp (T : Fin 3 → Fin 3 → (Wkp (volume : Measure R3) ballOpens 2 4 →L[ℝ]
      Wkp (volume : Measure R3) ballOpens 2 4)) (W : Wkp (volume : Measure R3) ballOpens 2 5)
    (t : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) :
    ⟪t, Wkp.value 3 (pertOp T W)⟫_ℝ =
      ∑ i : Fin 3, ∑ k : Fin 3, ⟪t, Wkp.value 3 (dL3 i (T i k (dL4 k W)))⟫_ℝ :=
  apply_sum_comp_scalar ((innerSL ℝ t).comp (Wkp.valueL (mu := (volume : Measure R3))
    (Omega := ballOpens) (p := 2) 3)) (dL3 (Ω := ballOpens)) T (dL4 (Ω := ballOpens)) W

theorem pertOp_identity (M : R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (T : Fin 3 → Fin 3 → (Wkp (volume : Measure R3) ballOpens 2 4 →L[ℝ]
      Wkp (volume : Measure R3) ballOpens 2 4))
    (hT : ∀ i k, ∀ f, ⇑(Wkp.value 4 (T i k f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
      fun x => (cutB x * M x i k) * Wkp.value 4 f x)
    (W : Wkp (volume : Measure R3) ballOpens 2 5) (φ : 𝓓(ballOpens, ℝ)) :
    ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (Wkp.firstOrder 4 W) x) =
      -∫ x in (ballOpens : Set R3), Wkp.value 3 (pertOp (Ω := ballOpens) T W) x * φ x := by
  have hterm := fun i k => pert_term_int M W φ i k (T i k) (hT i k)
  have hL : ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
        (W1p.gradient (Wkp.firstOrder 4 W) x) =
      ∑ i : Fin 3, ∑ k : Fin 3, ∫ x in (ballOpens : Set R3),
        fderiv ℝ (φ : R3 → ℝ) x (EuclideanSpace.single i 1) *
          (M x i k * W1p.gradient (Wkp.firstOrder 4 W) x k) := by
    rw [Finset.sum_congr rfl fun i _ => (integral_finsetSum _ fun k _ => (hterm i k).1).symm]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => (hterm i k).1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [HO.matrixBilinearForm_eq_sum, DirichletFamily.gradient_apply_coord]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hL, integral_lp_test, inner_value_pertOp]
  simp only [← integral_lp_test, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => (hterm i k).2


theorem exists_mul_family (s : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ M : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ M → ∀ δ : ℝ, 0 ≤ δ →
    (∀ i k : Fin 3, ∀ j ≤ s + 1, ∀ y ∈ closedBall (0 : R3) 2,
      ‖iteratedFDeriv ℝ j (fun y => M y i k) y‖ ≤ δ) →
    ∀ i k : Fin 3, ∃ T : Wkp (volume : Measure R3) ballOpens 2 s →L[ℝ]
      Wkp (volume : Measure R3) ballOpens 2 s,
      (∀ f, ⇑(Wkp.value s (T f)) =ᵐ[(volume : Measure R3).restrict ballOpens]
        fun x => (cutB x * M x i k) * Wkp.value s f x) ∧ ‖T‖ ≤ C * δ := by
  obtain ⟨Cc, hCc, hcut⟩ := cut_bound (s + 1)
  obtain ⟨Cm, hCm, hmul⟩ := DirichletFamily.mulAt (Ω := ballOpens) s
  refine ⟨Cm * Cc, by positivity, fun M hM δ hδ hMb i k => ?_⟩
  have hent : ContDiff ℝ ∞ (fun y => M y i k) := HO.contDiff_matrix_entry hM i k
  obtain ⟨T, hT, hTn⟩ := hmul _ (contDiff_cutB.mul hent) cutB.hasCompactSupport.mul_right
    (Cc * δ) (by positivity)
    (fun j hj x => hcut _ hent δ hδ (fun j hj y hy => hMb i k j hj y hy) j hj x)
  exact ⟨T, hT, hTn.trans (le_of_eq (by ring))⟩

theorem exists_pert_op : ∃ CP : ℝ, 0 ≤ CP ∧
    ∀ M : R3 → Matrix (Fin 3) (Fin 3) ℝ, ContDiff ℝ ∞ M → ∀ δ : ℝ, 0 ≤ δ →
    (∀ i k : Fin 3, ∀ j ≤ 5, ∀ y ∈ closedBall (0 : R3) 2,
      ‖iteratedFDeriv ℝ j (fun y => M y i k) y‖ ≤ δ) →
    ∃ T : Wkp (volume : Measure R3) ballOpens 2 5 →L[ℝ] Wkp (volume : Measure R3) ballOpens 2 3,
      ‖T‖ ≤ CP * δ ∧ ∀ (W : Wkp (volume : Measure R3) ballOpens 2 5) (φ : 𝓓(ballOpens, ℝ)),
        ∫ x in (ballOpens : Set R3), matrixBilinearForm (M x) (gradient (φ : R3 → ℝ) x)
            (W1p.gradient (Wkp.firstOrder 4 W) x) =
          -∫ x in (ballOpens : Set R3), Wkp.value 3 (T W) x * φ x := by
  obtain ⟨C4, hC4, hmul⟩ := exists_mul_family 4
  refine ⟨C4 * derivativeNormSum ballOpens, mul_nonneg hC4 derivativeNormSum_nonneg,
    fun M hM δ hδ hMb => ?_⟩
  choose T hT hTn using hmul M hM δ hδ hMb
  refine ⟨pertOp (Ω := ballOpens) T, ?_, fun W φ => pertOp_identity M T hT W φ⟩
  calc ‖pertOp (Ω := ballOpens) T‖ ≤ C4 * δ * derivativeNormSum ballOpens := norm_pertOp_le T hTn
    _ = C4 * derivativeNormSum ballOpens * δ := by ring

/-! ### The constant-coefficient a priori bound -/

theorem const_hcoeff (A₀ : Matrix (Fin 3) (Fin 3) ℝ) {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) (fun _ => A₀) lam Lam) :
    MemLp (fun x => energyIntegrand ((fun _ : R3 => A₀) x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens) :=
  memLp_energyIntegrand_of_bounds hell.upper_nonneg aestronglyMeasurable_const
    aestronglyMeasurable_const aestronglyMeasurable_const
    (fun _x hx eta xi => hell.upper_bound hx eta xi)
    (beta := 0) (gamma := 0) (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ))
    (fun _ _ => by simp) (fun _ _ => by simp)

theorem const_lower (A₀ : Matrix (Fin 3) (Fin 3) ℝ) {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) (fun _ => A₀) lam Lam) :
    ∀ w : BallH1Zero, lam ^ 2 / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1)) * ‖w‖ ^ 2 ≤
      energyFormH1 (fun _ : R3 => A₀) (0 : R3 → R3) (0 : R3 → ℝ) (w : BallH1) (w : BallH1) := by
  intro w
  have hn : ‖(w : BallH1)‖ = ‖w‖ := rfl
  have hb := hell.mul_norm_sq_le_energyFormH1_self_of_subset_ball
    aestronglyMeasurable_const aestronglyMeasurable_const aestronglyMeasurable_const
    (b := (0 : R3 → R3)) (c := (0 : R3 → ℝ)) (beta := 0) (gamma := 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ _ => by simp)
    (z := 0) (R := 1)
    (show (ballOpens : Set R3) ⊆ ball (0 : R3) 1 from Set.Subset.rfl) w.2
  rw [hn] at hb
  simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, sub_zero] using hb

theorem const_heq (A₀ : Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand ((fun _ : R3 => A₀) x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens))
    (f : Wkp (volume : Measure R3) ballOpens 2 3)
    (W : Wkp (volume : Measure R3) ballOpens 2 5)
    (hW0 : Wkp.firstOrder 4 W ∈ w1p0Submodule (volume : Measure R3) ballOpens 2)
    (hW : WeakEq (fun _ => A₀) (Wkp.value 3 f) (Wkp.firstOrder 4 W)) :
    ∀ v : BallH1Zero, energyFormH1L0 hcoeff ⟨Wkp.firstOrder 4 W, hW0⟩ v =
      dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) (Wkp.value 3 f) v := by
  intro v
  rw [Regularity.energyFormH1L0_eq_integral, dirichletForcing_apply_eq_setIntegral]
  exact Regularity.eq_of_testFunction continuous_const hW v v.2

theorem const_norm_le (A₀ : Matrix (Fin 3) (Fin 3) ℝ)
    (hcoeff : MemLp (fun x => energyIntegrand ((fun _ : R3 => A₀) x) 0 0) ⊤
      ((volume : Measure R3).restrict ballOpens)) {κ : ℝ} (hκ : 0 < κ)
    (hlower : ∀ w : BallH1Zero, κ * ‖w‖ ^ 2 ≤
      energyFormH1 (fun _ : R3 => A₀) (0 : R3 → R3) (0 : R3 → ℝ) (w : BallH1) (w : BallH1))
    (F : Lp ℝ 2 ((volume : Measure R3).restrict ballOpens)) (u : BallH1Zero)
    (heq : ∀ v : BallH1Zero, energyFormH1L0 hcoeff u v =
      dirichletForcing (mu := (volume : Measure R3)) (Omega := ballOpens) F v) :
    ‖u‖ ≤ ‖F‖ / κ := by
  have hsol : IsWeakSolutionDirichlet (fun _ : R3 => A₀) (0 : R3 → R3) (0 : R3 → ℝ) F u := by
    intro v
    exact (energyFormH1L0_apply hcoeff u v).symm.trans (heq v)
  exact norm_le_of_isWeakSolutionDirichlet hκ hlower hsol

theorem exists_const_bound (A₀ : Matrix (Fin 3) (Fin 3) ℝ) {lam Lam : ℝ}
    (hell : UniformlyEllipticOn (ballOpens : Set R3) (fun _ => A₀) lam Lam) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ (f : Wkp (volume : Measure R3) ballOpens 2 3)
      (W : Wkp (volume : Measure R3) ballOpens 2 5),
      Wkp.firstOrder 4 W ∈ w1p0Submodule (volume : Measure R3) ballOpens 2 →
      WeakEq (fun _ => A₀) (Wkp.value 3 f) (Wkp.firstOrder 4 W) → ‖W‖ ≤ C₀ * ‖f‖ := by
  have hcoeff := const_hcoeff A₀ hell
  obtain ⟨C, hC0, hC⟩ := DirichletFamily.fixedDirichletRegularity 3 (fun _ => A₀) lam Lam
    contDiffOn_const hell hcoeff
  have hlam : 0 < lam := hell.pos
  have hκ : 0 < lam ^ 2 / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1)) := by positivity
  refine ⟨C * (1 / (lam ^ 2 / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1))) + 1), by positivity,
    fun f W hW0 hW => ?_⟩
  have heq := const_heq A₀ hcoeff f W hW0 hW
  obtain ⟨U, hU, hUn⟩ := hC f ⟨Wkp.firstOrder 4 W, hW0⟩ heq
  have hUW : U = W := DirichletFamily.firstOrder_injective 4 hU
  have hun := const_norm_le A₀ hcoeff hκ (const_lower A₀ hell) _ _ heq
  have hfv : ‖Wkp.value 3 f‖ ≤ ‖f‖ := Wkp.norm_value_le 3 f
  have hn : ‖(Wkp.firstOrder 4 W : BallH1)‖ ≤ ‖f‖ / (lam ^ 2 / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1))) :=
    hun.trans (div_le_div_of_nonneg_right hfv hκ.le)
  rw [← hUW]
  calc ‖U‖ ≤ C * (‖(Wkp.firstOrder 4 W : BallH1)‖ + ‖f‖) := hUn
    _ ≤ C * (‖f‖ / (lam ^ 2 / (2 * lam * ((2 * (1 : ℝ)) ^ 2 + 1))) + ‖f‖) := by gcongr
    _ = _ := by ring

end OAI.AnisotropicCalderon.Regularity.Jets
