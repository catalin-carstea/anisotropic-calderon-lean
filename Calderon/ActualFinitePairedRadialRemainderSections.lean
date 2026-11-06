import Calderon.ActualFinitePairedRadialRemainderSmoothRoom
import Calderon.ActualFinitePairedRadialRemainderGraphRoom
import Calderon.ActualFiniteGaugePairedRadialRemainderDomain
import Calderon.ActualFiniteGaugeAdjointValueGraphTopology
import Calderon.ActualFinitePhysicalDomainCommonRoom
import Calderon.LocalSmoothSignedTaylorRemainder
import Calderon.SphereSobolevPartialSumOperator

/-! The current scalar coefficient is frozen during the auxiliary Taylor variable.
Only the original input is cut; both actual outputs remain uncompressed. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff ENNReal Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local instance referenceFinitePairedRadialRemainderSectionsHighCompleteSpace : CompleteSpace (SphereSobolev (3/2 : ℝ)) := by
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  exact lp.completeSpace

local instance referenceFinitePairedRadialRemainderSectionsHighOperatorCompleteSpace : CompleteSpace
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := by infer_instance

attribute [local irreducible] referenceFiniteHarmonicProductHighRadialFamily
  referenceFiniteGaugeAdjointRadialFamily referenceFiniteHarmonicProductHighSecondRemainder
  referenceFiniteGaugeAdjointSecondRemainder referenceStrongDriftFamily
  referenceSharpRadialTraceFamily referenceAdjointThreeHalfRadialFamily
  nativeThreeHalfCoefficientMulL sphereSobolevInclusionL

lemma contDiffAt_referenceFinitePairedRadialRemainder_currentCoefficient
    {K0 : Set (ℝ × (R3 × ℝ))}
    (G : ReferenceGaugeNormalReciprocalRoom g L Φ a K0) (n : ℕ) (q : ℝ)
    (m : R3 × R3 → ℝ) (hm : ContDiff ℝ ∞ m)
    (K : Set R3) (hK : IsCompact K) (hz : ∀ y x, x ∉ K → m (y,x)=0)
    (Q : R3 → SmoothCoefficientJets 3)
    (hQ : ∀ y, coefficientValue 3 (Q y) = fun x => m (y,x))
    (R : R3 → ℝ) (y : R3) (hR : ContDiffAt ℝ ∞ R y)
    (hSegment : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q
        (y,θ*R y)).IsInvertible) :
    ContDiffAt ℝ ∞ (fun x => referenceFiniteHarmonicProductHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q x) q x (R x)) y ∧
    ContDiffAt ℝ ∞ (fun x => referenceFiniteGaugeAdjointSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q x) q x (R x)) y := by
  let Qt : (ℝ × (R3 × ℝ)) → SmoothCoefficientJets 3 := fun p => Q p.2.1
  let mt : (ℝ × (R3 × ℝ)) × R3 → ℝ := fun z => m (z.1.2.1,z.2)
  have hmt : ContDiff ℝ ∞ mt :=
    hm.comp (contDiff_fst.snd.fst.prodMk contDiff_snd)
  have hzt : ∀ p x, x ∉ K → mt (p,x)=0 := fun p x hx => hz p.2.1 x hx
  have hQt : ∀ p, coefficientValue 3 (Qt p) = fun x => mt (p,x) :=
    fun p => hQ p.2.1
  let T : R3 × ℝ → ℝ × (R3 × ℝ) := fun z => (q,(z.1,z.2))
  have hT : ContDiff ℝ ∞ T := contDiff_const.prodMk (contDiff_fst.prodMk contDiff_snd)
  let Ω : Set (R3 × ℝ) := {z | (referenceStrongDriftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc 1 q (z.1,z.2)).IsInvertible}
  have hΩ : IsOpen Ω := by
    letI : CompleteSpace (StrongDirichletSpace 1) := instCompleteSpaceStrongDirichletSpace 1
    apply ContinuousLinearMap.isOpen_setOfPred_isInvertible.preimage
    exact ((contDiff_joint_referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1).comp
        (contDiff_const.prodMk contDiff_id)).continuous
  let FP : R3 × ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    fun z => referenceFiniteHarmonicProductHighRadialFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q z.1) (q,(z.1,z.2))
  let FA : R3 × ℝ → (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
    fun z => referenceFiniteGaugeAdjointRadialFamily
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q z.1) (q,(z.1,z.2))
  have hFP : ContDiffOn ℝ ∞ FP Ω := by
    intro z hzΩ
    have hRaw := contDiffAt_referenceFiniteHarmonicProductHighRadialFamily_of_value_graph
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n
        mt hmt K hK hzt Qt hQt (T z) hzΩ
    have hAt : ContDiffAt ℝ ∞ FP z := by
      simpa only [FP,Qt,T,Function.comp_def] using hRaw.comp z hT.contDiffAt
    exact hAt.contDiffWithinAt
  have hFA : ContDiffOn ℝ ∞ FA Ω := by
    intro z hzΩ
    have hRaw := contDiffAt_referenceFiniteGaugeAdjointRadialFamily_of_value_graph
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n
        mt hmt K hK hzt Qt hQt (T z) hzΩ
    have hAt : ContDiffAt ℝ ∞ FA z := by
      simpa only [FA,Qt,T,Function.comp_def] using hRaw.comp z hT.contDiffAt
    exact hAt.contDiffWithinAt
  have hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (y,θ*R y) ∈ Ω := hSegment
  have hP := (contDiffAt_secondTaylorRemainder_joint_of_open_segment
    FP Ω hΩ hFP y (R y) hSeg).comp y (contDiffAt_id.prodMk hR)
  have hA := (contDiffAt_secondTaylorRemainder_joint_of_open_segment
    FA Ω hΩ hFA y (R y) hSeg).comp y (contDiffAt_id.prodMk hR)
  constructor
  · simpa only [referenceFiniteHarmonicProductHighSecondRemainder,FP,Function.comp_def,id_eq] using hP
  · simpa only [referenceFiniteGaugeAdjointSecondRemainder,FA,Function.comp_def,id_eq] using hA

theorem exists_reference_commonRadius_finitePairedRadialRemainder_sections
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ dG δ : ℝ, 0 < dG ∧ dG ≤ ρ ∧ 0 < δ ∧ δ ≤ ρ ∧ δ ≤ dG ∧
      ∃ G : ReferenceGaugeNormalReciprocalRoom g L Φ a
          (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-(2*dG)) (2*dG))),
      ∀ (n : ℕ) (q : ℝ), q ∈ Icc (0 : ℝ) 1 →
      ∀ (R : R3 → ℝ), ContDiff ℝ ∞ R →
      ∀ (m : R3 × R3 → ℝ), ContDiff ℝ ∞ m →
      ∀ (K : Set R3), IsCompact K → (∀ y x, x ∉ K → m (y,x)=0) →
      ∀ (Q : R3 → SmoothCoefficientJets 3),
      (∀ y, coefficientValue 3 (Q y) = fun x => m (y,x)) →
      ∀ (u : R3 → SphereSobolev (3/2 : ℝ)), ContDiff ℝ ∞ u → HasCompactSupport u →
      (∀ y ∈ tsupport u, ‖y-y0‖ < ρ ∧ |R y| < δ) →
        let ηP : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
          referenceFiniteHarmonicProductHighSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q y) q y (R y) (u y)
        let ηA : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
          referenceFiniteGaugeAdjointSecondRemainder
            g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q y) q y (R y) (u y)
        let z : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
          nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (Q y)
            (sphereSobolevPartialSum (3/2 : ℝ) n (u y))
        let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
        ContDiff ℝ ∞ ηP ∧ ContDiff ℝ ∞ ηA ∧
        tsupport ηP ⊆ tsupport u ∧ tsupport ηA ⊆ tsupport u ∧
        HasCompactSupport ηP ∧ HasCompactSupport ηA ∧
        ∀ y : R3,
          I (ηP y) = secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y) (z y) ∧
          I (ηA y) = secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
            g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y) (z y) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS GLOBAL_ENTER"
    out.flush
  let room := Classical.choice
    (exists_referenceFinitePairedRadialRemainderSmoothRoom
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel)
  let dP : ℝ := room.graphRoom.primalRadius
  let dA : ℝ := room.graphRoom.adjointRadius
  let dRoom : ℝ := room.strongRadius
  let δ : ℝ := room.commonRadius
  let G := room.graphRoom.gauge
  have hdA : 0 < dA := room.graphRoom.adjointRadius_pos
  have hdAρ : dA ≤ ρ := room.graphRoom.adjointRadius_le
  have hδEq : δ = min dP (min dA dRoom) := room.commonRadius_eq
  have hδ : 0 < δ := room.commonRadius_pos
  have hδP : δ ≤ dP := room.commonRadius_le_primal
  have hδA : δ ≤ dA := room.commonRadius_le_adjoint
  have hδRoom : δ ≤ dRoom := room.commonRadius_le_strong
  have hδρ : δ ≤ ρ := room.commonRadius_le
  have hPrimal := room.graphRoom.primalGraph
  have hAdjoint := room.graphRoom.adjointGraph
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS SMOOTH_ROOM_READY"
    out.flush
  refine ⟨dA,δ,hdA,hdAρ,hδ,hδρ,hδA,G,?_⟩
  intro n q hq R hR m hm K hK hz Q hQ u hu hCompact hSupportRoom
  let ηP : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
    referenceFiniteHarmonicProductHighSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 n (Q y) q y (R y) (u y)
  let ηA : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
    referenceFiniteGaugeAdjointSecondRemainder
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n (Q y) q y (R y) (u y)
  let z : R3 → SphereSobolev (3/2 : ℝ) := fun y =>
    nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0 (Q y)
      (sphereSobolevPartialSum (3/2 : ℝ) n (u y))
  let I := sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS INPUTS_AND_SECTIONS_READY"
    out.flush
  have hSupportP : tsupport ηP ⊆ tsupport u := by
    apply closure_minimal ?_ (isClosed_tsupport u)
    intro y hy
    by_contra hyu
    have hZero : u y = 0 := image_eq_zero_of_notMem_tsupport hyu
    apply hy
    simp only [ηP,hZero,map_zero]
  have hSupportA : tsupport ηA ⊆ tsupport u := by
    apply closure_minimal ?_ (isClosed_tsupport u)
    intro y hy
    by_contra hyu
    have hZero : u y = 0 := image_eq_zero_of_notMem_tsupport hyu
    apply hy
    simp only [ηA,hZero,map_zero]
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS SUPPORT_READY"
    out.flush
  have hSegment (y : R3) (hy : y ∈ tsupport u) : ∀ θ ∈ Icc (0 : ℝ) 1,
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc 1 q
        (y,θ*R y)).IsInvertible := by
    intro θ hθ
    have hAt := hSupportRoom y hy
    have hθabs : |θ| ≤ 1 := by rw [abs_of_nonneg hθ.1]; exact hθ.2
    have hθR : |θ*R y| ≤ dRoom := by
      calc
        _ = |θ| * |R y| := abs_mul _ _
        _ ≤ 1 * |R y| := mul_le_mul_of_nonneg_right hθabs (abs_nonneg _)
        _ ≤ dRoom := by simpa only [one_mul] using hAt.2.le.trans hδRoom
    have hp : (q,(y,θ*R y)) ∈
        Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-dRoom) dRoom) := by
      refine ⟨hq,?_,abs_le.mp hθR⟩
      simpa only [mem_closedBall,dist_eq_norm] using hAt.1.le
    exact room.strongInverse (q,(y,θ*R y)) hp
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS SEGMENT_READY"
    out.flush
  have hSmoothP : ContDiff ℝ ∞ ηP := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hOps := contDiffAt_referenceFinitePairedRadialRemainder_currentCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n q
          m hm K hK hz Q hQ R y hR.contDiffAt (hSegment y hy)
      exact hOps.1.clm_apply hu.contDiffAt
    · have hyP : y ∉ tsupport ηP := fun h => hy (hSupportP h)
      have hZero : ηP =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyP
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) y).congr_of_eventuallyEq hZero
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS PRIMAL_SMOOTH_READY"
    out.flush
  have hSmoothA : ContDiff ℝ ∞ ηA := by
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ tsupport u
    · have hOps := contDiffAt_referenceFinitePairedRadialRemainder_currentCoefficient
        g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 G n q
          m hm K hK hz Q hQ R y hR.contDiffAt (hSegment y hy)
      exact hOps.2.clm_apply hu.contDiffAt
    · have hyA : y ∉ tsupport ηA := fun h => hy (hSupportA h)
      have hZero : ηA =ᶠ[𝓝 y] (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) :=
        notMem_tsupport_iff_eventuallyEq.mp hyA
      exact (contDiffAt_const : ContDiffAt ℝ ∞
        (fun _ : R3 => (0 : SphereSobolev (3/2 : ℝ))) y).congr_of_eventuallyEq hZero
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS ADJOINT_SMOOTH_READY"
    out.flush
  refine ⟨hSmoothP,hSmoothA,hSupportP,hSupportA,
    hCompact.of_isClosed_subset (isClosed_tsupport ηP) hSupportP,
    hCompact.of_isClosed_subset (isClosed_tsupport ηA) hSupportA,?_⟩
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SECTIONS ALLPOINT_GRAPH_ENTER"
    out.flush
  intro y
  by_cases hy : y ∈ tsupport u
  · run_tac do
      let out ← IO.getStdout
      out.putStrLn "LA-SECTIONS ONSUPPORT_GRAPH_ENTER"
      out.flush
    have hAt := hSupportRoom y hy
    exact ⟨hPrimal q hq y hAt.1.le (R y) (hAt.2.le.trans hδP) n (Q y) (u y),
      hAdjoint q hq y hAt.1.le (R y) (hAt.2.le.trans hδA) n (Q y) (u y)⟩
  · run_tac do
      let out ← IO.getStdout
      out.putStrLn "LA-SECTIONS ZERO_GRAPH_ENTER"
      out.flush
    have hZero : u y = 0 := image_eq_zero_of_notMem_tsupport hy
    have hPZero : ηP y = 0 := by simp only [ηP,hZero,map_zero]
    have hAZero : ηA y = 0 := by simp only [ηA,hZero,map_zero]
    have hzZero : z y = 0 := by
      simp only [z,hZero,← sphereSobolevPartialSumL_apply,map_zero]
    constructor
    · change I (ηP y) =
        secondTaylorRemainder (fun t : ℝ => referenceSharpRadialTraceFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y) (z y)
      simp only [hPZero,hzZero,map_zero]
    · change I (ηA y) =
        secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
          g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (q,(y,t))) (R y) (z y)
      simp only [hAZero,hzZero,map_zero]

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceFinitePairedRadialRemainder_currentCoefficient
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_reference_commonRadius_finitePairedRadialRemainder_sections
