import Calderon.ActualUpperAnnularSeedDensity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError ConformalDepth
  ActualScalarPrincipalAdjoint SphereHarmonic ReferenceWeightedApproximation MetricOperator MetricVolume
attribute [local irreducible] nativeMixedKernelHighDensity nativeMixedKernelPullbackHkDatum
  referencePhysicalGaugeConormalDensity

theorem exists_uniform_nativeMixedKernelHighDensity_annular_firstJet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam a b : ℝ) (C : NativeNormalCover S L)
    (Hext : R3 × R3 → ℝ) (hHext : ContDiff ℝ ∞ Hext) :
    ∃ B0 : ℝ, 1 ≤ B0 ∧ ∀ i : Fin C.count, ∀ y ∈ cylinder, ∀ r ∈ Icc a b,
      ‖nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
        (C.packet i) Hext hHext (lam,(y,r))‖ ≤ B0 ∧
      ‖fderiv ℝ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
        (C.packet i) Hext hHext) (lam,(y,r))‖ ≤ B0 := by
  let F (i : Fin C.count) := nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L
    (C.packet i) Hext hHext
  let K : Set (ℝ × R3) := Icc a b ×ˢ cylinder
  have hK : IsCompact K := isCompact_Icc.prod isCompact_native_center_cylinder
  have hParam : Continuous (fun v : ℝ × R3 => (lam,(v.2,v.1))) :=
    continuous_const.prodMk (continuous_snd.prodMk continuous_fst)
  have hSmooth (i : Fin C.count) : ContDiff ℝ ∞ (F i) :=
    contDiff_nativeMixedKernelHighDensity hcalc hreg hF hO hD τ0 S L
      (C.packet i) Hext hHext
  have hFirst (i : Fin C.count) : ContDiff ℝ ∞ (fderiv ℝ (F i)) :=
    (hSmooth i).fderiv_right (m := ∞) (by simp)
  have hTuple (i : Fin C.count) : Continuous
      (fun v : ℝ × R3 => (F i (lam,(v.2,v.1)),fderiv ℝ (F i) (lam,(v.2,v.1)))) :=
    ((hSmooth i).continuous.comp hParam).prodMk ((hFirst i).continuous.comp hParam)
  have hBounds : ∀ i : Fin C.count, ∃ M : ℝ, ∀ v ∈ K,
      ‖(F i (lam,(v.2,v.1)),fderiv ℝ (F i) (lam,(v.2,v.1)))‖ ≤ M := by
    intro i
    exact hK.exists_bound_of_continuousOn (hTuple i).continuousOn
  choose M hBound using hBounds
  obtain ⟨B0,hB0⟩ := (Set.finite_range M).bddAbove
  refine ⟨max B0 1,le_max_right _ _,?_⟩
  intro i y hy r hr
  have h : ‖(F i (lam,(y,r)),fderiv ℝ (F i) (lam,(y,r)))‖ ≤ max B0 1 :=
    (hBound i (r,y) ⟨hr,hy⟩).trans ((hB0 ⟨i,rfl⟩).trans (le_max_left _ _))
  simpa only [Prod.norm_def,max_le_iff] using h

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
