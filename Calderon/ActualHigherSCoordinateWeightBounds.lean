import Calderon.ActualHigherSLeadingBracketGain
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoordinateWeightBounds
open EnergyBridge ConnectionError ActualHigherSLeadingBracketGain

/-- The exact contracted weight on its true radius-independent base variables. -/
def coordinateWeightBase (g g2 : MatrixField) (L : ℝ) (l a : Fin 3) (z : ℝ × R3) : ℝ :=
  firstCoordinateWeight g g2 L l a ((z.1,(z.2,0)),0)

theorem firstCoordinateWeight_eq_base (g g2 : MatrixField) (L : ℝ) (l a : Fin 3)
    (t : (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)) :
    firstCoordinateWeight g g2 L l a t = coordinateWeightBase g g2 L l a (t.1.1,t.1.2.1) := rfl

theorem physical_firstCoordinateWeight_eq_base (g g2 : MatrixField)
    (L dr Ar q : ℝ) (p : ℕ) (l a : Fin 3) :
    (fun x => firstCoordinateWeight g g2 L l a (ActualHigherSFormation.higherSParam L dr Ar p q x)) =
      (fun x : R3 => coordinateWeightBase g g2 L l a (q,x)) := rfl

theorem contDiff_coordinateWeightBase (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (l a : Fin 3) :
    ContDiff ℝ ∞ (coordinateWeightBase g g2 L l a) := by
  unfold coordinateWeightBase firstCoordinateWeight
  exact ContDiff.sum (fun m _ =>
    (ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L m l).mul
      ((contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L m a).add
        (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L a m)))

/-- Elementary finite compact-family bound; same proof as Root's adjoint coefficient bounds. -/
private theorem compact_family_cap {X V I : Type*} [TopologicalSpace X]
    [SeminormedAddCommGroup V] [Fintype I] (K : Set X) (hK : IsCompact K)
    (f : I → X → V) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ i : I, ∀ x ∈ K, ‖f i x‖ ≤ M := by
  classical
  choose C hC using fun i : I => hK.exists_bound_of_continuousOn (hf i)
  have hs0 : 0 ≤ ∑ i : I, |C i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨1+∑ i : I, |C i|,by linarith,?_⟩
  intro i x hx
  apply (hC i x hx).trans
  calc
    C i ≤ |C i| := le_abs_self _
    _ ≤ ∑ j : I, |C j| := Finset.single_le_sum (f := fun j : I => |C j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    _ ≤ 1+∑ j : I, |C j| := by linarith

/-- One cap is chosen before every q, base point, radius profile and angular input. -/
theorem exists_coordinateWeightBase_uniform_first_caps (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (y0 : R3) (rho : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 rho,
      ∀ l a : Fin 3, |coordinateWeightBase g g2 L l a (q,x)| ≤ M ∧
        ‖fderiv ℝ (coordinateWeightBase g g2 L l a) (q,x)‖ ≤ M := by
  let K := Icc (0 : ℝ) 1 ×ˢ closedBall y0 rho
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_closedBall y0 rho)
  let f : (Fin 3 × Fin 3) → (ℝ × R3) → ℝ := fun i => coordinateWeightBase g g2 L i.1 i.2
  have hf (i : Fin 3 × Fin 3) : ContDiff ℝ ∞ (f i) :=
    contDiff_coordinateWeightBase g g2 hg hg2 L i.1 i.2
  obtain ⟨M0,hM0,h0⟩ := compact_family_cap K hK f (fun i => (hf i).continuous.continuousOn)
  obtain ⟨M1,hM1,h1⟩ := compact_family_cap K hK (fun i => fderiv ℝ (f i))
    (fun i => ((hf i).fderiv_right (m := ∞) (by simp)).continuous.continuousOn)
  refine ⟨M0+M1,by linarith,?_⟩
  intro q hq x hx l a
  have h0' := h0 (l,a) (q,x) ⟨hq,hx⟩
  have h1' := h1 (l,a) (q,x) ⟨hq,hx⟩
  change ‖coordinateWeightBase g g2 L l a (q,x)‖ ≤ M0 at h0'
  change ‖fderiv ℝ (coordinateWeightBase g g2 L l a) (q,x)‖ ≤ M1 at h1'
  rw [Real.norm_eq_abs] at h0'
  exact ⟨by linarith,by linarith⟩

/-- The fixed-q slice costs at most one in the canonical product norm. -/
theorem norm_fderiv_fixed_q_slice_le (f : ℝ × R3 → ℝ) (hf : ContDiff ℝ ∞ f)
    (q : ℝ) (x : R3) (M : ℝ) (hM : 0 ≤ M) (hcap : ‖fderiv ℝ f (q,x)‖ ≤ M) :
    ‖fderiv ℝ (fun y : R3 => f (q,y)) x‖ ≤ M := by
  have ht : HasFDerivAt (fun y : R3 => (q,y)) (ContinuousLinearMap.inr ℝ ℝ R3) x :=
    (hasFDerivAt_const q x).prodMk (hasFDerivAt_id x)
  have hd := ((hf.differentiable (by simp) (q,x)).hasFDerivAt.comp x ht).fderiv
  refine ContinuousLinearMap.opNorm_le_bound _ hM (fun v => ?_)
  have hdu : fderiv ℝ (fun y : R3 => f (q,y)) x v = fderiv ℝ f (q,x) (0,v) :=
    congrArg (fun A : R3 →L[ℝ] ℝ => A v) hd
  rw [hdu]
  calc
    _ ≤ ‖fderiv ℝ f (q,x)‖*‖((0,v) : ℝ × R3)‖ := (fderiv ℝ f (q,x)).le_opNorm _
    _ = ‖fderiv ℝ f (q,x)‖*‖v‖ := by simp only [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg v)]
    _ ≤ M*‖v‖ := mul_le_mul_of_nonneg_right hcap (norm_nonneg v)

/-- Actual profile weights have uniform value/first-physical-derivative caps without radius hypotheses. -/
theorem exists_physical_firstCoordinateWeight_uniform_first_caps (g g2 : MatrixField)
    (hg : IsAdmissibleMetric g) (hg2 : IsAdmissibleMetric g2) (L : ℝ) (y0 : R3) (rho : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ q ∈ Icc (0 : ℝ) 1, ∀ x ∈ closedBall y0 rho,
      ∀ dr Ar : ℝ, ∀ p : ℕ, ∀ l a : Fin 3,
      let f := fun y => firstCoordinateWeight g g2 L l a (ActualHigherSFormation.higherSParam L dr Ar p q y)
      ContDiff ℝ ∞ f ∧ |f x| ≤ M ∧ ‖fderiv ℝ f x‖ ≤ M := by
  obtain ⟨M,hM,hcap⟩ := exists_coordinateWeightBase_uniform_first_caps g g2 hg hg2 L y0 rho
  refine ⟨M,hM,?_⟩
  intro q hq x hx dr Ar p l a
  dsimp only
  rw [physical_firstCoordinateWeight_eq_base]
  have hf := contDiff_coordinateWeightBase g g2 hg hg2 L l a
  exact ⟨hf.comp (contDiff_const.prodMk contDiff_id), (hcap q hq x hx l a).1,
    norm_fderiv_fixed_q_slice_le _ hf q x M (by linarith) (hcap q hq x hx l a).2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSCoordinateWeightBounds
