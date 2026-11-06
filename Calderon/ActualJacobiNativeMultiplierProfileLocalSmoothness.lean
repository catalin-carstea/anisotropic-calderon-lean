import Calderon.ActualJacobiThreeHalfBoundaryMultiplierFamily
import Calderon.ActualJacobiCoefficientTubeCover

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic MetricOperator NormalCoordinatesFrame
  NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier

local instance referenceJacobiProfileOpenRoomHighIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (3/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceJacobiProfileOpenRoomHalfIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (1/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ))

local instance referenceJacobiProfileOpenRoomNegativeIsBoundedSMul :
    IsBoundedSMul ℝ (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) :=
  @NormedSpace.toIsBoundedSMul ℝ
    (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) Real.normedField
    (ContinuousLinearMap.toSeminormedAddCommGroup
      (E := SphereSobolev (-(1/2 : ℝ))) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))
    (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (-(1/2 : ℝ))) (F := SphereSobolev (-(1/2 : ℝ)))
      (σ₁₂ := RingHom.id ℝ))

theorem exists_referenceJacobiNativeMultiplier_profile_open_room
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (y0 : R3)
    (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
    (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
    (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
    (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace) :
    let V : Set (ℝ × (R3 × ℝ)) := {p | ∀ ξ : UnitSphere,
      (referenceFramedNormalizedJacobian g L Φ (p.1,(p.2,ξ.val))).IsInvertible}
    let Nhi : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (3/2 : ℝ)) := fun i j z =>
      nativeThreeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryThreeHalfCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nhalf : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (1/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) := fun i j z =>
      nativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    let Nneg : Fin 3 → Fin 3 → (ℝ × (R3 × ℝ)) →
        (SphereSobolev (-(1/2 : ℝ)) →L[ℝ] SphereSobolev (-(1/2 : ℝ))) := fun i j z =>
      nativeNegativeHalfCoefficientMulL hcalc hF hO hD τ0
        (referenceJacobiBoundaryCoefficientFamily
          g hg L y0 Φ B ε C ρ H a w hData i j z)
    IsOpen V ∧ ∃ d : ℝ, 0 < d ∧ d ≤ ρ ∧ d ≤ 1 ∧
      (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ⊆ V ∧
      ∀ q ∈ Icc (0 : ℝ) 1, ∀ R : R3 → ℝ, ContDiff ℝ ∞ R →
      ∀ s : ℝ, |s| ≤ 1 →
      let U : Set R3 := {x | (q,(x,s*R x)) ∈ V}
      IsOpen U ∧ (∀ x ∈ closedBall y0 ρ, |R x| ≤ d → x ∈ U) ∧
      ∀ power : ℕ, ∀ i j : Fin 3,
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Nhi i j (q,(x,s*R x))) U ∧
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Nhalf i j (q,(x,s*R x))) U ∧
        ContDiffOn ℝ ∞ (fun x => (s*R x)^power • Nneg i j (q,(x,s*R x))) U := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "JACOBI_PROFILE_OPEN_ROOM_BODY"
    out.flush
  intro V Nhi Nhalf Nneg
  have hΘ : ContDiff ℝ ∞ (fun p : ℝ × (R3 × R3) => (Φ p.1 p.2 1).1) :=
    hData.1.1.1.2.2.2.2.2.2.2.1
  let T : (ℝ × (R3 × ℝ)) × R3 → ReferenceEndpointVariables :=
    fun t => (t.1.1,(t.1.2,t.2))
  have hT : ContDiff ℝ ∞ T :=
    contDiff_fst.fst.prodMk (contDiff_fst.snd.prodMk contDiff_snd)
  let J : (ℝ × (R3 × ℝ)) × R3 → R3 →L[ℝ] R3 :=
    fun t => referenceFramedNormalizedJacobian g L Φ (T t)
  have hJ : ContDiff ℝ ∞ J :=
    (contDiff_referenceFramedNormalizedJacobian g hg L Φ hΘ).comp hT
  let S : Set ((ℝ × (R3 × ℝ)) × R3) := {t | (J t).IsInvertible}
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    exact hJ.continuous.continuousAt.eventually ht.eventually_nhds
  have hV : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hTube : ∀ᶠ p in 𝓝 z, ∀ ξ ∈ sphere (0 : R3) 1, (p,ξ) ∈ S := by
      apply (isCompact_sphere (0 : R3) 1).eventually_forall_of_forall_eventually
      intro ξ hξ
      exact hS.mem_nhds (hz ⟨ξ,hξ⟩)
    exact hTube.mono (fun p hp ξ => hp ξ.val ξ.property)
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "JACOBI_PROFILE_OPEN_ROOM_SPHERE_OPEN"
    out.flush
  have hHi (i j : Fin 3) : ContDiffOn ℝ ∞ (Nhi i j) V := by
    intro z hz
    exact (contDiffAt_nativeThreeHalf_referenceJacobiBoundaryThreeHalfCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z hz).contDiffWithinAt
  have hHalf (i j : Fin 3) : ContDiffOn ℝ ∞ (Nhalf i j) V := by
    intro z hz
    exact (contDiffAt_nativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z hz).contDiffWithinAt
  have hNeg (i j : Fin 3) : ContDiffOn ℝ ∞ (Nneg i j) V := by
    intro z hz
    exact (contDiffAt_nativeNegativeHalf_referenceJacobiBoundaryCoefficientFamily
      g hg L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 i j z hz).contDiffWithinAt
  let d : ℝ := min ρ 1
  have hd : 0 < d := lt_min hData.1.2.1 (by norm_num)
  have hdρ : d ≤ ρ := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  have hCover : (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-d) d)) ⊆ V :=
    referenceFramedNormalizedJacobian_isInvertible_on_actual_coefficient_tube
      g L y0 Φ B ε C ρ H a w hData d hd hdρ
  refine ⟨hV,d,hd,hdρ,hd1,hCover,?_⟩
  intro q hq R hR s hs U
  let χ : R3 → ℝ × (R3 × ℝ) := fun x => (q,(x,s*R x))
  have hχ : ContDiff ℝ ∞ χ :=
    contDiff_const.prodMk (contDiff_id.prodMk (contDiff_const.mul hR))
  have hU : IsOpen U := hV.preimage hχ.continuous
  have hMap : MapsTo χ U V := fun x hx => hx
  refine ⟨hU,?_,?_⟩
  · intro x hx hRx
    have hsr : |s*R x| ≤ d := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans
        (by simpa only [one_mul] using hRx)
    exact hCover ⟨hq,hx,abs_le.mp hsr⟩
  · intro power i j
    have hPow : ContDiff ℝ ∞ (fun x => (s*R x)^power) := (contDiff_const.mul hR).pow power
    have hHiU : ContDiffOn ℝ ∞ (fun x => Nhi i j (χ x)) U :=
      (hHi i j).comp hχ.contDiffOn hMap
    have hHalfU : ContDiffOn ℝ ∞ (fun x => Nhalf i j (χ x)) U :=
      (hHalf i j).comp hχ.contDiffOn hMap
    have hNegU : ContDiffOn ℝ ∞ (fun x => Nneg i j (χ x)) U :=
      (hNeg i j).comp hχ.contDiffOn hMap
    run_tac do
      let out ← IO.getStdout
      out.putStrLn "JACOBI_PROFILE_OPEN_ROOM_PROFILE_LOCAL_READY"
      out.flush
    exact ⟨hPow.contDiffOn.smul hHiU,hPow.contDiffOn.smul hHalfU,
      hPow.contDiffOn.smul hNegU⟩

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.exists_referenceJacobiNativeMultiplier_profile_open_room
