import Calderon.ActualReferenceRadialEndpointOpenLocus
import Calderon.ActualReferenceAdjointRadialEndpointConstruction
import Calderon.ActualAdjointMovingBoundaryFamilyFoundation
import Calderon.JointRadialDerivativeLocalSmoothness
import Calderon.LocalSmoothSignedTaylorRemainder
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Monoid

/-! Full upfront written before this source: FULL-UPFRONT-EXPANSION.md,
SHA256 55e78bb41b0d892a66c12a3beefe54c13f7d163c28ad66879cc39baa2ec71020.
Author-only proposal under Root v165. No native or proof-acceptance claim. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

/- The identical complete canonical-completeness proof passed in isolation
   (source63919da7); it is proved here, not imported as a new premise. -/
private theorem completeSpace_sphereSobolev_threeHalf_to_half :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    CompleteSpace (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := by
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI : ∀ k : ℕ, CompleteSpace (harmonicSphereSubspace k) :=
    instCompleteSpaceHarmonicSphereSubspace
  letI : CompleteSpace (SphereSobolev (1/2 : ℝ)) := lp.completeSpace
  letI productsOperatorCompleteSpace : CompleteSpace
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.instCompleteSpace
      (𝕜₁ := ℝ) (𝕜₂ := ℝ) (σ := RingHom.id ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
  exact productsOperatorCompleteSpace

/-- Complete actual signed tube, Taylor continuity and zero-slice regularity. -/
theorem exists_referencePhysicalDensityProducts_static_regularity
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
    let D : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let T : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) ⊆ Ω) ∧
      ContinuousOn T (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ∧
      ContinuousOn (fun b : ℝ × R3 => D (b.1,(b.2,0)))
        (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) ∧
      (∀ i : Fin 3, ContinuousOn (fun b : ℝ × R3 => C0 i (b.1,(b.2,0)))
        (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ)) := by
  classical
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI : CompleteSpace
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    completeSpace_sphereSobolev_threeHalf_to_half
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let HH : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
    referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
  let D : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    deriv (fun t : ℝ => HH (z.1,(z.2.1,t))) z.2.2
  let T : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    secondTaylorRemainder (fun t : ℝ => HH (z.1,(z.2.1,t))) z.2.2
  change ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) ⊆ Ω) ∧
      ContinuousOn T (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ∧
      ContinuousOn (fun b : ℝ × R3 => D (b.1,(b.2,0)))
        (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ) ∧
      (∀ i : Fin 3, ContinuousOn (fun b : ℝ × R3 => C0 i (b.1,(b.2,0)))
        (Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ))
  obtain ⟨δ,hδ,hδρ,hδΩ⟩ :=
    exists_reference_commonRadius_subset_radialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let d : ℝ := min δ 1
  have hd : 0 < d := lt_min hδ zero_lt_one
  have hdδ : d ≤ δ := min_le_left _ _
  have hdρ : d ≤ ρ := hdδ.trans hδρ
  have hd1 : d ≤ 1 := min_le_right _ _
  let K0 : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  let K : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  have hKΩ : K ⊆ Ω := by
    intro z hz
    apply hδΩ
    exact ⟨hz.1,hz.2.1,⟨by linarith [hz.2.2.1],hz.2.2.2.trans hdδ⟩⟩
  have hΩ : IsOpen Ω :=
    isOpen_referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  have hHH : ContDiffOn ℝ ∞ HH Ω :=
    contDiffOn_referenceAdjointThreeHalfRadialFamily_invertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  have hDerivSmooth : ContDiffOn ℝ ∞ D Ω := contDiffOn_deriv_joint_radialSlice HH Ω hΩ hHH
  let A : ((ℝ × R3) × ℝ) → ℝ × (R3 × ℝ) := fun z => (z.1.1,(z.1.2,z.2))
  let BB : (ℝ × (R3 × ℝ)) → (ℝ × R3) × ℝ := fun z => ((z.1,z.2.1),z.2.2)
  have hA : ContDiff ℝ ∞ A := by
    exact (contDiff_fst.fst).prodMk ((contDiff_fst.snd).prodMk contDiff_snd)
  have hBB : ContDiff ℝ ∞ BB := by
    exact (contDiff_fst.prodMk (contDiff_snd.fst)).prodMk (contDiff_snd.snd)
  let Ω' : Set ((ℝ × R3) × ℝ) := A ⁻¹' Ω
  have hΩ' : IsOpen Ω' := hΩ.preimage hA.continuous
  have hHH' : ContDiffOn ℝ ∞ (HH ∘ A) Ω' :=
    hHH.comp hA.contDiffOn (fun _ hz => hz)
  have hTAt (z : ℝ × (R3 × ℝ)) (hz : z ∈ K) : ContDiffAt ℝ ∞ T z := by
    have hSegment : ∀ θ ∈ Icc (0 : ℝ) 1, ((z.1,z.2.1),θ*z.2.2) ∈ Ω' := by
      intro θ hθ
      apply hKΩ
      refine ⟨hz.1,hz.2.1,?_⟩
      have habs : |θ*z.2.2| ≤ d := by
        rw [abs_mul,abs_of_nonneg hθ.1]
        exact (mul_le_mul_of_nonneg_right hθ.2 (abs_nonneg _)).trans
          (by simpa only [one_mul] using abs_le.mpr hz.2.2)
      exact abs_le.mp habs
    have hLocal := contDiffAt_secondTaylorRemainder_joint_of_open_segment
      (HH ∘ A) Ω' hΩ' hHH' (z.1,z.2.1) z.2.2 hSegment
    simpa only [T,A,BB,Function.comp_def] using hLocal.comp z hBB.contDiffAt
  have hTCont : ContinuousOn T K := fun z hz => (hTAt z hz).continuousAt.continuousWithinAt
  let Z : (ℝ × R3) → ℝ × (R3 × ℝ) := fun b => (b.1,(b.2,0))
  have hZ : ContDiff ℝ ∞ Z :=
    contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const)
  have hZK (b : ℝ × R3) (hb : b ∈ K0) : Z b ∈ K :=
    ⟨hb.1,hb.2,⟨by linarith [hd],hd.le⟩⟩
  have hCCont (i : Fin 3) : ContinuousOn (fun b : ℝ × R3 => C0 i (Z b)) K0 := by
    intro b hb
    have hC := contDiffAt_referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg (Z b) i (hKΩ (hZK b hb))
    exact (hC.comp b hZ.contDiffAt).continuousAt.continuousWithinAt
  have hDCont : ContinuousOn (fun b : ℝ × R3 => D (Z b)) K0 :=
    hDerivSmooth.continuousOn.comp' hZ.continuous.continuousOn (fun b hb => hKΩ (hZK b hb))
  refine ⟨d,hd,hdρ,hd1,hKΩ,hTCont,?_,?_⟩
  · simpa only [Z] using hDCont
  · intro i
    simpa only [Z] using hCCont i

/-- One complete norm-only compact bound, specialized below at the original CLM dictionary. -/
private theorem exists_compact_three_norm_bounds
    {X Y V : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [instV : NormedAddCommGroup V]
    (K : Set X) (K0 : Set Y) (hK : IsCompact K) (hK0 : IsCompact K0)
    (T : X → V) (D : Y → V) (C : Fin 3 → Y → V)
    (hT : ContinuousOn T K) (hD : ContinuousOn D K0)
    (hC : ∀ i : Fin 3, ContinuousOn (C i) K0) :
    ∃ M : ℝ, 0 < M ∧
      (∀ x ∈ K, ‖T x‖ ≤ M/2) ∧
      (∀ y ∈ K0, (∀ i : Fin 3, ‖C i y‖ ≤ M) ∧ ‖D y‖ ≤ M) := by
  classical
  have hCsumCont : ContinuousOn (fun y : Y => ∑ i : Fin 3, ‖C i y‖) K0 :=
    continuousOn_finsetSum _ (fun i _ => (hC i).norm)
  obtain ⟨BC,hBC⟩ := hK0.exists_bound_of_continuousOn hCsumCont
  obtain ⟨BD,hBD⟩ := hK0.exists_bound_of_continuousOn hD
  obtain ⟨BT,hBT⟩ := hK.exists_bound_of_continuousOn hT
  let MC : ℝ := |BC|
  let MD : ℝ := |BD|
  let MT : ℝ := |BT|
  have hMC : 0 ≤ MC := abs_nonneg _
  have hMD : 0 ≤ MD := abs_nonneg _
  have hMT : 0 ≤ MT := abs_nonneg _
  have hCcap (y : Y) (hy : y ∈ K0) (i : Fin 3) : ‖C i y‖ ≤ MC := by
    have hOne : ‖C i y‖ ≤ ∑ j : Fin 3, ‖C j y‖ :=
      Finset.single_le_sum (fun j _ => norm_nonneg (C j y)) (Finset.mem_univ i)
    have hScalar : |∑ j : Fin 3, ‖C j y‖| ≤ BC := by
      simpa only [Real.norm_eq_abs] using hBC y hy
    exact hOne.trans ((le_abs_self _).trans (hScalar.trans (le_abs_self BC)))
  have hDcap (y : Y) (hy : y ∈ K0) : ‖D y‖ ≤ MD :=
    (hBD y hy).trans (le_abs_self BD)
  have hTcap (x : X) (hx : x ∈ K) : ‖T x‖ ≤ MT :=
    (hBT x hx).trans (le_abs_self BT)
  let M : ℝ := 1+MC+MD+2*MT
  have hM : 0 < M := by dsimp only [M]; linarith
  have hCM : MC ≤ M := by dsimp only [M]; linarith
  have hDM : MD ≤ M := by dsimp only [M]; linarith
  have hTM : MT ≤ M/2 := by dsimp only [M]; linarith
  refine ⟨M,hM,?_,?_⟩
  · intro x hx
    exact (hTcap x hx).trans hTM
  · intro y hy
    exact ⟨fun i => (hCcap y hy i).trans hCM,(hDcap y hy).trans hDM⟩

/-- Actual signed-tube and zero-slice static bounds for the original Products estimate. -/
theorem exists_referencePhysicalDensityProducts_static_compact_bounds
    (g : MatrixField) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (hreg : FixedDirichletRegularity) :
    letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedAddCommGroup
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
      ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
        (σ₁₂ := RingHom.id ℝ)
    let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
    let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
      referenceHighAdjointCoordinateBoundaryFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
    let D : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      deriv (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    let T : (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
      secondTaylorRemainder (fun t : ℝ => referenceAdjointThreeHalfRadialFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 (z.1,(z.2.1,t))) z.2.2
    ∃ d M : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ 0 < M ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) ⊆ Ω) ∧
      (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ‖T z‖ ≤ M/2) ∧
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
        (∀ i : Fin 3, ‖C0 i (q,(y,0))‖ ≤ M) ∧ ‖D (q,(y,0))‖ ≤ M) := by
  classical
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  let Ω : Set (ℝ × (R3 × ℝ)) := referenceRadialEndpointInvertibleLocus
    g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let HH : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    referenceAdjointThreeHalfRadialFamily g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
  let C0 : Fin 3 → (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i z =>
    referenceHighAdjointCoordinateBoundaryFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 z i
  let D : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    deriv (fun t : ℝ => HH (z.1,(z.2.1,t))) z.2.2
  let T : (ℝ × (R3 × ℝ)) →
      (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun z =>
    secondTaylorRemainder (fun t : ℝ => HH (z.1,(z.2.1,t))) z.2.2
  change ∃ d M : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧ 0 < M ∧
    (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d) ⊆ Ω) ∧
    (∀ z ∈ Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d), ‖T z‖ ≤ M/2) ∧
    (∀ q ∈ Icc (0 : ℝ) 1, ∀ y ∈ closedBall y0 ρ,
      (∀ i : Fin 3, ‖C0 i (q,(y,0))‖ ≤ M) ∧ ‖D (q,(y,0))‖ ≤ M)
  obtain ⟨d,hd,hdρ,hd1,hKΩRaw,hTContRaw,hDContRaw,hCContRaw⟩ :=
    exists_referencePhysicalDensityProducts_static_regularity
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 hreg
  let K0 : Set (ℝ × R3) := Icc (0 : ℝ) 1 ×ˢ closedBall y0 ρ
  let K : Set (ℝ × (R3 × ℝ)) :=
    Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)
  let Z : (ℝ × R3) → ℝ × (R3 × ℝ) := fun b => (b.1,(b.2,0))
  have hKΩ : K ⊆ Ω := hKΩRaw
  have hTCont : ContinuousOn T K := hTContRaw
  have hDCont : ContinuousOn (fun b : ℝ × R3 => D (Z b)) K0 := hDContRaw
  have hCCont (i : Fin 3) : ContinuousOn (fun b : ℝ × R3 => C0 i (Z b)) K0 :=
    hCContRaw i
  have hK0 : IsCompact K0 := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hK : IsCompact K :=
    isCompact_Icc.prod ((isCompact_closedBall _ _).prod isCompact_Icc)
  obtain ⟨M,hM,hTcap,hCDcap⟩ :=
    exists_compact_three_norm_bounds
      (X := ℝ × (R3 × ℝ)) (Y := ℝ × R3)
      (V := SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ))
      (instV := productsOperatorNormedAddCommGroup)
      K K0 hK hK0 T (fun b => D (Z b)) (fun i b => C0 i (Z b))
      hTCont hDCont hCCont
  refine ⟨d,M,hd,hdρ,hd1,hM,hKΩ,hTcap,?_⟩
  intro q hq y hy
  exact hCDcap (q,y) ⟨hq,hy⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePhysicalDensityProducts_static_regularity

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referencePhysicalDensityProducts_static_compact_bounds
