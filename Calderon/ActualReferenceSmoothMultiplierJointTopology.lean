import Calderon.NativeSmoothMultiplierForcingTopology
import Calderon.ActualReferenceSmoothMultiplierBoundaryCommutator
import Calderon.ActualReferenceCoordinateCorrectionTopology
import Calderon.CompactInverseDerivativeBounds

/-! Common-support commutator jets. The actual reference
parameter and genuine compact multiplier-extension parameter remain independent. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (Kq : Set R3) (hKq : IsCompact Kq)
  (hqz : ∀ t x, x ∉ Kq → q (t,x) = 0)

lemma contDiff_referenceSmoothMultiplierForcing_commonSupport_joint
    (hcalc : FixedSobolevCalculus) :
    ContDiff ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceSmoothMultiplierCommutatorForcingFamily g L y0 Φ B ε C ρ H a w hData hcalc
        (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) := by
  let ha := jointReferenceStrongCoefficient_data g L y0 Φ B ε C ρ H a w hData
  let hb := jointReferenceWeightedDrift_data g L y0 Φ B ε C ρ H a w hData
  let A : ((ℝ × (R3 × ℝ)) × T) × R3 → Matrix (Fin 3) (Fin 3) ℝ :=
    fun z => a (z.1.1,z.2)
  let b : ((ℝ × (R3 × ℝ)) × T) × R3 → R3 :=
    fun z => conformalReferenceWeightedFramedDrift g L Φ H w (z.1.1,z.2)
  let m : ((ℝ × (R3 × ℝ)) × T) × R3 → ℝ := fun z => q (z.1.2,z.2)
  have hA : ContDiff ℝ ∞ A := ha.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hb' : ContDiff ℝ ∞ b := hb.1.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hm : ContDiff ℝ ∞ m := hq.comp (contDiff_fst.snd.prodMk contDiff_snd)
  exact contDiff_nativeBulkMultiplierCommutatorForcingL_of_joint_graphs hcalc A b m hA hb' hm
    (closedBall (0 : R3) 3) (isCompact_closedBall _ _)
    (fun z x hx => ha.2.2.2.1 z.1 x hx) (fun z x hx => hb.2 z.1 x hx)
    (fun z => referenceCoordinateForcingPrincipalJets g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => referenceCoordinateForcingDriftJets g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2)
    (fun z => coefficientMatrixField_referenceCoordinateForcingPrincipalJets
      g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => nativeSmoothDriftField_referenceCoordinateForcingDriftJets
      g L y0 Φ B ε C ρ H a w hData z.1)
    (fun z => by funext x; exact coefficientValue_commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2 x)

lemma contDiff_nativeHalfNormalDerivativeMulL_commonSupport
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    ContDiff ℝ ∞ (fun t => nativeHalfNormalDerivativeMulL hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 q hq Kq hKq hqz t)) := by
  have hterm (i : Fin 3) : ContDiff ℝ ∞ (fun t => nativeHalfCoefficientMulL hcalc hF hO hD τ0
      (smoothMultiplierDerivativeJets (commonSupportCoefficientFamily 3 q hq Kq hKq hqz t) i)) := by
    have he : (fun t => nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (smoothMultiplierDerivativeJets (commonSupportCoefficientFamily 3 q hq Kq hKq hqz t) i)) =
        fun t => nativeHalfCoefficientMulL hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 2 (smoothMultiplierSpatialDerivative q i)
            (contDiff_smoothMultiplierSpatialDerivative q hq i) Kq hKq
            (smoothMultiplierSpatialDerivative_zero_outside q hq Kq hKq hqz i) t) := by
      funext t
      rw [smoothMultiplierDerivativeJets_commonSupport]
    rw [he]
    exact contDiff_nativeHalfCoefficientMulL_commonSupport hcalc hF hO hD τ0
      (smoothMultiplierSpatialDerivative q i) (contDiff_smoothMultiplierSpatialDerivative q hq i)
      Kq hKq (smoothMultiplierSpatialDerivative_zero_outside q hq Kq hKq hqz i)
  unfold nativeHalfNormalDerivativeMulL
  exact ContDiff.sum (fun i hi => contDiff_const.clm_comp (hterm i))

lemma contDiffAt_referenceSmoothMultiplierStrongDefect_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceSmoothMultiplierStrongDefectFamily g L y0 Φ B ε C ρ H a w hData hcalc hF
        (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) (p,t) := by
  letI : CompleteSpace (StrongDirichletSpace 0) := instCompleteSpaceStrongDirichletSpace 0
  have hA := contDiff_joint_referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0
  have hInv : ContDiffAt ℝ ∞ (fun u : ℝ × (R3 × ℝ) =>
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 0 u.1 u.2).inverse) p := by
    have hMap := hStrong.contDiffAt_map_inverse (n := ∞)
    try simp only [real_nontriviallyNormedField_normedField_eq,
      submodule_normedAddCommGroup_seminormedAddCommGroup_eq,
      clm_normedAddCommGroup_seminormedAddCommGroup_eq,normedAddCommGroup_ofSeparation_eq,
      submodule_seminormedAddCommGroup_topologicalSpace_eq,
      submodule_seminormedAddCommGroup_addCommMonoid_eq,submodule_normedSpace_module_eq,
      lp_normedAddCommGroup_addCommMonoid_eq,lp_normedSpace_module_eq,
      clm_seminormedAddCommGroup_topologicalSpace_eq,
      clm_seminormedAddCommGroup_addCommMonoid_eq,clm_normedSpace_module_eq] at hMap
    simpa only [Function.comp_def] using hMap.comp p hA.contDiffAt
  have hInvJoint := hInv.comp (p,t) contDiffAt_fst
  have hQ := contDiff_referenceSmoothMultiplierForcing_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc
  have hW := (contDiffAt_referenceWeakHalfLiftFamily_of_isInvertible
    g L y0 Φ B ε C ρ H a w hData hcalc hF p hWeak).comp (p,t) contDiffAt_fst
  unfold referenceSmoothMultiplierStrongDefectFamily
  exact contDiffAt_const.clm_comp (hInvJoint.clm_comp (hQ.contDiffAt.clm_comp hW))

lemma contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible)
    (hWeak : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc p).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      referenceSmoothMultiplierBoundaryCommutatorFamily g L y0 Φ B ε C ρ H a w hData
        hcalc hF hO hD τ0 (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1) (p,t) := by
  have hV := contDiffAt_referenceSmoothMultiplierStrongDefect_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc hF p t hStrong hWeak
  have hN := (contDiff_nativeHalfNormalDerivativeMulL_commonSupport
    q hq Kq hKq hqz hcalc hF hO hD τ0).contDiffAt.comp (p,t) contDiffAt_snd
  unfold referenceSmoothMultiplierBoundaryCommutatorFamily
  exact (contDiffAt_const.clm_comp hV).add hN

attribute [local irreducible] referenceSmoothMultiplierBoundaryCommutatorFamily
  referenceRadialEndpointInvertibleLocus referenceStrongDriftFamily
  referenceWeakDirichletEnergyFamily referenceNormalBoundaryMultiplierFamily

lemma exists_reference_commonRadius_smoothMultiplierBoundaryCommutator_joint_jets
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) (Kt : Set T) (hKt : IsCompact Kt) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧ ∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧
      ∀ z ∈ (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) ×ˢ Kt,
        z.1 ∈ referenceRadialEndpointInvertibleLocus
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 ∧
        ∀ k : ℕ, k ≤ N → ‖iteratedFDeriv ℝ k
          (fun u : (ℝ × (R3 × ℝ)) × T => referenceSmoothMultiplierBoundaryCommutatorFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
              (commonSupportCoefficientFamily 3 q hq Kq hKq hqz u.2) u.1) z‖ ≤ M := by
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hRadius : ∃ δ : ℝ, 0 < δ ∧ δ ≤ ρ ∧
      Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ) ⊆ Ω :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  obtain ⟨δ,hδ,hδρ,hRoom⟩ := hRadius
  let K : Set ((ℝ × (R3 × ℝ)) × T) :=
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-δ) δ)) ×ˢ Kt
  let F : ((ℝ × (R3 × ℝ)) × T) →
      SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ) :=
    fun u => referenceSmoothMultiplierBoundaryCommutatorFamily
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
      (commonSupportCoefficientFamily 3 q hq Kq hKq hqz u.2) u.1
  have hK : IsCompact K :=
    (isCompact_Icc.prod ((isCompact_closedBall y0 ρ).prod isCompact_Icc)).prod hKt
  have hSmooth : ∀ z ∈ K, ContDiffAt ℝ ∞ F z := by
    intro z hz
    have hi := hRoom hz.1
    change z.1 ∈ referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 at hi
    unfold referenceRadialEndpointInvertibleLocus at hi
    exact contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
      g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc hF hO hD τ0 z.1 z.2 hi.1 hi.2.1
  refine ⟨δ,hδ,hδρ,?_⟩
  intro N
  obtain ⟨M,hM,hBound⟩ := exists_compact_iteratedFDeriv_bound F K hK hSmooth N
  refine ⟨M,hM,?_⟩
  intro z hz
  exact ⟨hRoom hz.1,fun k hk => hBound k hk z hz⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_referenceSmoothMultiplierForcing_commonSupport_joint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiff_nativeHalfNormalDerivativeMulL_commonSupport
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothMultiplierStrongDefect_commonSupport_joint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceSmoothMultiplierBoundaryCommutator_commonSupport_joint
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_smoothMultiplierBoundaryCommutator_joint_jets
