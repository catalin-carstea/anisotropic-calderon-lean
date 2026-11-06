import Calderon.ActualJacobiHighPhysicalRoomCoercivity
import Calderon.ActualJacobiCommonSupportMultiplierGerms

/-! Root direct compact extension construction of the EXACT X5 Pi scalar.
Full expansion before-source-v001/UPFRONT.md precedes this source. -/
set_option autoImplicit false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeCoefficientBoundaryMultiplier NativeThreeHalfCoefficientMultiplier
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)

def referencePiScalarCoefficient (g : MatrixField) (L : ℝ)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (i : Fin 3) (z : Tpar × R3) : ℝ :=
  z.2 i + z.1.1.2.2^2 * (∑ j : Fin 3, z.2 j *
    referenceFramedJacobiVelocityRemainder g L Φ i (z.1.1.1,(z.1.1.2,z.2)) j) +
  z.1.2 (conformalReferenceGramFrameOperatorJoint g L (z.1.1.1,z.1.1.2.1) (coordinateVector i))

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

include hData in
theorem exists_referencePi_commonSupport_coefficient_germs
    (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus) (hreg : FixedDirichletRegularity)
    (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (τ0 : UnitBallValueTrace) :
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧
    ∃ (m : Fin 3 → Tpar × R3 → ℝ) (hm : ∀ i, ContDiff ℝ ∞ (m i))
      (Km : Set R3) (hKm : IsCompact Km)
      (hmz : ∀ i t x, x ∉ Km → m i (t,x) = 0),
      ∀ i : Fin 3, ∀ t ∈
        (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ×ˢ
          closedBall (0 : R3 →L[ℝ] ℝ) 1,
        ∀ᶠ z in 𝓝 t, ∀ x : UnitSphere,
          coefficientValue 3 (commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hmz i) z) x.val =
            referencePiScalarCoefficient g L Φ i (z,x.val) ∧
          (referenceFramedNormalizedJacobian g L Φ (z.1.1,(z.1.2,x.val))).IsInvertible := by
  classical
  obtain ⟨d,hd,hdρ,hRoom⟩ := exists_reference_commonRadius_jacobiHighPhysicalRoom
    g L y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  let Kp : Set Pphys := Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  let Kt : Set Tpar := Kp ×ˢ closedBall (0 : R3 →L[ℝ] ℝ) 1
  have hKp : IsCompact Kp := isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  have hKt : IsCompact Kt := hKp.prod (isCompact_closedBall _ _)
  have hTheta : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : Tpar × R3 → ReferenceEndpointVariables := fun z => (z.1.1.1,(z.1.1.2,z.2))
  have hT : ContDiff ℝ ∞ T := contDiff_fst.fst.fst.prodMk
    (contDiff_fst.fst.snd.prodMk contDiff_snd)
  let J : Tpar × R3 → R3 →L[ℝ] R3 := fun z => referenceFramedNormalizedJacobian g L Φ (T z)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hTheta).comp hT
  let Ω : Set (Tpar × R3) := {z | (J z).IsInvertible}
  have hΩ : IsOpen Ω := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    exact hJ.continuous.continuousAt.eventually hz.eventually_nhds
  have hCover : ∀ t ∈ Kt, ∀ x : UnitSphere, (t,x.val) ∈ Ω := by
    intro t ht x
    exact (hRoom t.1 ht.1).2.2 x
  have hSmooth (i : Fin 3) : ContDiffOn ℝ ∞ (referencePiScalarCoefficient g L Φ i) Ω := by
    intro z hz
    have hN (j : Fin 3) : ContDiffAt ℝ ∞
        (fun u : Tpar × R3 => referenceFramedJacobiVelocityRemainder g L Φ i (T u) j) z :=
      ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.contDiffAt).comp z
        ((contDiffAt_referenceFramedJacobiVelocityRemainder g hg L Φ hTheta i (T z) hz).comp z hT.contDiffAt)
    have hX (j : Fin 3) : ContDiffAt ℝ ∞ (fun u : Tpar × R3 => u.2 j) z :=
      ((EuclideanSpace.proj j : R3 →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
    have hR : ContDiffAt ℝ ∞ (fun u : Tpar × R3 => u.1.1.2.2) z := contDiffAt_fst.fst.snd.snd
    have hFrame : ContDiffAt ℝ ∞ (fun u : Tpar × R3 =>
        conformalReferenceGramFrameOperatorJoint g L (u.1.1.1,u.1.1.2.1) (coordinateVector i)) z :=
      (((contDiff_conformalReferenceGramFrameOperatorJoint g hg L).comp
        (contDiff_fst.fst.fst.prodMk contDiff_fst.fst.snd.fst)).clm_apply contDiff_const).contDiffAt
    have hEll : ContDiffAt ℝ ∞ (fun u : Tpar × R3 =>
        u.1.2 (conformalReferenceGramFrameOperatorJoint g L (u.1.1.1,u.1.1.2.1) (coordinateVector i))) z :=
      contDiffAt_fst.snd.clm_apply hFrame
    have hSum : ContDiffAt ℝ ∞ (fun u : Tpar × R3 =>
        ∑ j : Fin 3, u.2 j * referenceFramedJacobiVelocityRemainder g L Φ i (T u) j) z :=
      ContDiffAt.sum fun j _ => (hX j).mul (hN j)
    exact ((hX i).add ((hR.pow 2).mul hSum)).add hEll |>.contDiffWithinAt
  have hEach (i : Fin 3) := exists_contDiff_commonSupport_eq_near_compact_sphere
    Kt hKt Ω hΩ (referencePiScalarCoefficient g L Φ i) (hSmooth i) hCover
  choose m hm Ki hKi hmz hNear using hEach
  let Km : Set R3 := ⋃ i : Fin 3, Ki i
  have hKm : IsCompact Km := isCompact_iUnion hKi
  have hZero : ∀ i t x, x ∉ Km → m i (t,x) = 0 := by
    intro i t x hx
    exact hmz i t x (fun hi => hx (mem_iUnion.mpr ⟨i,hi⟩))
  refine ⟨d,hd,hdρ,m,hm,Km,hKm,hZero,?_⟩
  intro i t ht
  filter_upwards [hNear i t ht] with z hz
  intro x
  exact ⟨(coefficientValue_commonSupportCoefficientFamily 3 (m i) (hm i) Km hKm (hZero i) z x.val).trans
    (hz x).1,(hz x).2⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
