import Calderon.ActualMixedKernelSurfaceHomotopyRoom
import Calderon.NativeSmoothBallSobolevFamily
import Calderon.ActualReferenceGaugePrincipalFamily

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError SphereHarmonic
  ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

def nativeMixedKernelPullbackJoint (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ)
    (v : (ℝ × (R3 × ℝ)) × R3) : ℝ :=
  Gext (packetEndpoint S L P v.1.1 v.1.2.1 v.1.2.2 v.2,v.1.2.1)

theorem contDiff_nativeMixedKernelPullbackJoint (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) :
    ContDiff ℝ ∞ (nativeMixedKernelPullbackJoint S L P Gext) := by
  have hTheta : ContDiff ℝ ∞ (fun v : ℝ × (R3 × R3) => (P.Phi v.1 v.2 1).1) :=
    P.native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : ContDiff ℝ ∞ (fun v : (ℝ × (R3 × ℝ)) × R3 =>
      packetEndpoint S L P v.1.1 v.1.2.1 v.1.2.2 v.2) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd))
  exact hG.comp (hX.prodMk contDiff_fst.snd.fst)

def nativeMixedKernelPullbackDatum (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (v : ℝ × (R3 × ℝ)) : SmoothData :=
  ⟨fun z => nativeMixedKernelPullbackJoint S L P Gext (v,z),
    SpatialJetFields.contDiff_spatial_slice (nativeMixedKernelPullbackJoint S L P Gext)
      (contDiff_nativeMixedKernelPullbackJoint S L P Gext hG) v⟩

def nativeMixedKernelPullbackHkDatum (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (k : ℕ) (v : ℝ × (R3 × ℝ)) : BallSobolev k :=
  smoothBallSobolev k (nativeMixedKernelPullbackDatum S L P Gext hG v)

theorem contDiff_nativeMixedKernelPullbackHkDatum
    (hcalc : FixedSobolevCalculus) (S : KnownSideSourceData) (L : ℝ)
    (P : NativeNormalPacket S L) (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (k : ℕ) :
    ContDiff ℝ ∞ (nativeMixedKernelPullbackHkDatum S L P Gext hG k) :=
  contDiff_smoothBallSobolev_of_joint hcalc k (nativeMixedKernelPullbackJoint S L P Gext)
    (contDiff_nativeMixedKernelPullbackJoint S L P Gext hG)

theorem exists_native_mixed_kernel_smooth_pullback_Hk_datum
    (hcalc : FixedSobolevCalculus) (S : KnownSideSourceData)
    (L lam delta Rstar bound separation : ℝ) (p : ℕ) (cover : NativeNormalCover S L)
    (K : ConstructedMixedKernel S L lam delta Rstar bound separation p cover)
    (hdelta : 0 < delta) (hRstar : 0 < Rstar)
    (i : Fin cover.count) (y : R3) (hy : y ∈ cylinder ∩ (cover.packet i).centers) :
    ∃ (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext), HasCompactSupport Gext ∧
      (∀ k : ℕ, ContDiff ℝ ∞ (nativeMixedKernelPullbackHkDatum S L (cover.packet i) Gext hG k)) ∧
      ∃ Y : Set R3, IsOpen Y ∧ y ∈ Y ∧ ∀ y' ∈ Y, ∀ z ∈ sphere (0 : R3) 1,
        (nativeMixedKernelPullbackDatum S L (cover.packet i) Gext hG
          (lam,(y',referenceRadius delta Rstar p L y'))).1 =ᶠ[𝓝 z]
        (fun w => K.kernel
          (packetEndpoint S L (cover.packet i) lam y' (referenceRadius delta Rstar p L y') w,y')) := by
  obtain ⟨Gext,Y,hG,hGc,hY,hyY,hRoom⟩ :=
    exists_smooth_mixed_kernel_eq_near_native_surface_homotopy S L lam delta Rstar bound separation
      p cover K hdelta hRstar i y hy
  refine ⟨Gext,hG,hGc,fun k => contDiff_nativeMixedKernelPullbackHkDatum hcalc S L (cover.packet i) Gext hG k,
    Y,hY,hyY,?_⟩
  intro y' hy' z hz
  let v : ℝ × (R3 × ℝ) := (lam,(y',referenceRadius delta Rstar p L y'))
  let X : R3 → R3 := packetEndpoint S L (cover.packet i) lam y' (referenceRadius delta Rstar p L y')
  have hEq : Gext =ᶠ[𝓝 (X z,y')] K.kernel := by
    have h := (hRoom y' hy' 1 ⟨zero_le_one,le_rfl⟩ z hz).2
    simpa only [sub_self,zero_smul,one_smul,zero_add,zero_mul,one_mul] using h
  have hTheta : ContDiff ℝ ∞ (fun t : ℝ × (R3 × R3) => ((cover.packet i).Phi t.1 t.2 1).1) :=
    (cover.packet i).native_data.1.1.1.2.2.2.2.2.2.2.1
  have hX : Continuous X :=
    ((contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L (cover.packet i).Phi hTheta).comp
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))).continuous
  have hT : Tendsto (fun w : R3 => (X w,y')) (𝓝 z) (𝓝 (X z,y')) :=
    (hX.prodMk continuous_const).tendsto z
  exact hEq.comp_tendsto hT


/-- The actual high density for the SAME smooth kernel pullback datum. -/
def nativeMixedKernelHighDensity
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext)
    (v : ℝ × (R3 × ℝ)) : SphereSobolev (3/2 : ℝ) :=
  referencePhysicalGaugeConormalDensity S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho
    P.H P.a P.w P.native_data hcalc hF hO hD τ0
    (nativeMixedKernelPullbackHkDatum S L P Gext hG 3) v

theorem contDiff_nativeMixedKernelHighDensity
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) :
    ContDiff ℝ ∞ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG) := by
  have hE := contDiff_nativeMixedKernelPullbackHkDatum hcalc S L P Gext hG 3
  have hDens := contDiffOn_referencePhysicalGaugeConormalDensity
    S.g1 S.g1_admissible L P.y0 P.Phi P.B P.epsGeo P.Cgeo P.rho P.H P.a P.w P.native_data
      hcalc hreg hF hO hD τ0 (nativeMixedKernelPullbackHkDatum S L P Gext hG 3) Set.univ hE.contDiffOn
  exact contDiffOn_univ.mp hDens

attribute [local irreducible] nativeMixedKernelHighDensity nativeMixedKernelPullbackHkDatum
  referencePhysicalGaugeConormalDensity referencePhysicalGaugeCoefficientJets

theorem contDiff_nativeMixedKernelHighDensity_profile
    (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (S : KnownSideSourceData) (L lam delta Rstar : ℝ) (p : ℕ) (P : NativeNormalPacket S L)
    (Gext : R3 × R3 → ℝ) (hG : ContDiff ℝ ∞ Gext) (hdelta : 0 < delta) (hRstar : 0 < Rstar) :
    ContDiff ℝ ∞ (fun y => nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG
      (lam,(y,referenceRadius delta Rstar p L y))) := by
  have hDens : ContDiff ℝ ∞ (nativeMixedKernelHighDensity hcalc hF hO hD τ0 S L P Gext hG) :=
    contDiff_nativeMixedKernelHighDensity hcalc hreg hF hO hD τ0 S L P Gext hG
  have hR : ContDiff ℝ ∞ (referenceRadius delta Rstar p L) :=
    contDiff_referenceRadius_actual delta Rstar p L hdelta hRstar
  have hParam : ContDiff ℝ ∞ (fun y : R3 => (lam,(y,referenceRadius delta Rstar p L y))) :=
    contDiff_const.prodMk (contDiff_id.prodMk hR)
  exact hDens.comp hParam

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
