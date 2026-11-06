import Calderon.ReferencePhysicalPoissonDensity
import Calderon.ActualKnownSidePoissonDensity
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter MeasureTheory
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ConnectionError
open EnergyBridge MetricOperator MetricVolume DirichletFamily DirichletFamily.DriftBootstrap
  SphereHarmonic
attribute [local irreducible] referencePhysicalPoissonDensity
variable (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

variable (hcalc : FixedSobolevCalculus)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
    (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)

include hg hData hcalc in
theorem exists_compact_uniform_referencePhysicalPoissonDensity_firstJet_bound
    (hreg : FixedDirichletRegularity) (K : Set (ℝ × (R3 × ℝ))) (hK : IsCompact K) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ p ∈ K,
      ‖referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 p‖ ≤ C0 ∧
      ‖fderiv ℝ (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0) p‖ ≤ C0 := by
  have hPi := contDiff_referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hD : ContDiff ℝ ∞ (fderiv ℝ (referencePhysicalPoissonDensity g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0)) :=
    hPi.fderiv_right (m := ∞) (by simp)
  obtain ⟨C1,hC1⟩ := hK.exists_bound_of_continuousOn hPi.continuous.continuousOn
  obtain ⟨C2,hC2⟩ := hK.exists_bound_of_continuousOn hD.continuous.continuousOn
  refine ⟨max (max C1 C2) 1,le_max_right _ _,?_⟩
  intro p hp
  exact ⟨(hC1 p hp).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hC2 p hp).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

theorem exists_uniform_nativeCover_referencePhysicalPoissonDensity_firstJet_bound
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) (S : MixedKernelConstructionTask.KnownSideSourceData)
    (L : ℝ) (cover : MixedKernelConstructionTask.NativeNormalCover S L) :
    ∃ C0 : ℝ, 1 ≤ C0 ∧ ∀ (i : Fin cover.count) (q : ℝ), q ∈ Icc (0:ℝ) 1 →
      ∀ y : R3, ‖y-(cover.packet i).y0‖ ≤ 4*(cover.packet i).rho →
      ∀ r : ℝ, |r| ≤ 4*(cover.packet i).rho →
      ‖referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0 (q,(y,r))‖ ≤ C0 ∧
      ‖fderiv ℝ (referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0) (q,(y,r))‖ ≤ C0 := by
  let family (i : Fin cover.count) := referencePhysicalPoissonDensity S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data hcalc hF hO hD τ0
  let K (i : Fin cover.count) : Set (ℝ × (R3 × ℝ)) := Icc (0:ℝ) 1 ×ˢ
    (closedBall (cover.packet i).y0 (4*(cover.packet i).rho) ×ˢ
      Icc (-4*(cover.packet i).rho) (4*(cover.packet i).rho))
  have hK (i : Fin cover.count) : IsCompact (K i) :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hBounds : ∀ i : Fin cover.count, ∃ M : ℝ, 1 ≤ M ∧
      ∀ t ∈ K i, ‖family i t‖ ≤ M ∧ ‖fderiv ℝ (family i) t‖ ≤ M := by
    intro i
    exact exists_compact_uniform_referencePhysicalPoissonDensity_firstJet_bound
      S.g1 S.g1_admissible L (cover.packet i).y0 (cover.packet i).Phi
      (cover.packet i).B (cover.packet i).epsGeo (cover.packet i).Cgeo (cover.packet i).rho
      (cover.packet i).H (cover.packet i).a (cover.packet i).w (cover.packet i).native_data
      hcalc hF hO hD τ0 hreg (K i) (hK i)
  choose M hM hBound using hBounds
  obtain ⟨C0,hC0⟩ := (Set.finite_range M).bddAbove
  refine ⟨max C0 1,le_max_right _ _,?_⟩
  intro i q hq y hy r hr
  have hMi : M i ≤ max C0 1 := (hC0 ⟨i,rfl⟩).trans (le_max_left _ _)
  have hp : (q,(y,r)) ∈ K i := by
    refine ⟨hq,?_,?_⟩
    · simpa only [mem_closedBall,dist_eq_norm] using hy
    · change -4*(cover.packet i).rho ≤ r ∧ r ≤ 4*(cover.packet i).rho
      exact ⟨by linarith [(abs_le.mp hr).1],(abs_le.mp hr).2⟩
  exact ⟨((hBound i _ hp).1).trans hMi,((hBound i _ hp).2).trans hMi⟩

end OAI.AnisotropicCalderon.ConnectionError
