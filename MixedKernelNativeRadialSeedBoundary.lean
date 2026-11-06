import MixedKernelNativeRadialCoordinates
import MixedKernelNativeIntermediateFront
import Mathlib.Topology.Order.Compact
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology InnerProductSpace

/-- The actual velocity norm on the SAME entire native front is the original positive radius. -/
theorem nativeVelocityInverse_norm_on_nativeSphereFront
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (hd : 0 < delta) (hRs : 0 < Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < R)
    (q : R3 × R3) (hq : q ∈ nativeSphereFront S L C lam delta Rstar p) :
    ‖(nativeVelocityInverse S L C lam R q).2‖ = referenceRadius delta Rstar p L q.2 := by
  have hZero := nativeGlobalEnergy_zero_on_nativeSphereFront S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius q hq
  unfold nativeGlobalEnergy at hZero
  rw [real_inner_self_eq_norm_sq] at hZero
  apply (sq_eq_sq₀ (norm_nonneg _) (referenceRadius_pos delta Rstar p L q.2 hd hRs).le).mp
  linarith only [hZero]

/-- A positive retained tail is fixed BEFORE arbitrary delta and lies below BOTH original seed margins. -/
theorem exists_native_radial_initial_seed_tail
    (L Rstar : ℝ) (p : ℕ) (hL : 0 < L) (hRs : 0 < Rstar) :
    ∃ tail : ℝ, 0 < tail ∧ tail < Rstar*(depthPrimitive L (1/8) (1/4))^p ∧
      ∀ y ∈ cylinder, 2*tail < referenceRadius 1 Rstar p L y := by
  obtain ⟨m,hm,Hm⟩ := isCompact_cylinder.exists_forall_le'
    (contDiff_referenceRadius_actual 1 Rstar p L (by norm_num) hRs).continuous.continuousOn
    (fun y _ => referenceRadius_pos 1 Rstar p L y (by norm_num) hRs)
  let u := Rstar*(depthPrimitive L (1/8) (1/4))^p
  have hu : 0 < u := mul_pos hRs (pow_pos (depthPrimitive_quarter_pos L hL) p)
  let tail := min u m/4
  have hTail : 0 < tail := div_pos (lt_min hu hm) (by norm_num)
  have huCap : tail ≤ u/4 := div_le_div_of_nonneg_right (min_le_left u m) (by norm_num)
  have hmCap : tail ≤ m/4 := div_le_div_of_nonneg_right (min_le_right u m) (by norm_num)
  refine ⟨tail,hTail,by linarith,?_⟩
  intro y hy
  have hh := Hm y hy
  linarith

/-- The genuine delta=1 outside is contained in the ACTUAL fixed tail seed. -/
theorem nativeRadialOutsideRoom_one_subset_nativeRadialSeedRoom
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0 < R) (hRoom : R < C.radiusCeiling)
    (Rstar tail : ℝ) (p : ℕ) (hRs : 0 < Rstar)
    (hTail : ∀ y ∈ cylinder, tail < referenceRadius 1 Rstar p L y) :
    nativeRadialOutsideRoom S L C lam R 1 Rstar p ⊆ nativeRadialSeedRoom S L C lam R tail := by
  rintro q ⟨a,ha,rfl⟩
  have hVel : a ∈ nativeNormalVelocityRoom S L C R :=
    ⟨ha.1.1,by simpa only [mem_ball,dist_zero_right] using ha.2.2⟩
  have hInv := nativeVelocityInverse_left S L C lam hlam R hR hRoom a hVel
  have hFar : tail < ‖a.2‖ :=
    (hTail a.1 (interior_subset ha.1.2)).trans ha.2.1
  have hv : a.2 ≠ 0 := norm_ne_zero_iff.mp
    ((referenceRadius_pos 1 Rstar p L a.1 (by norm_num) hRs).trans ha.2.1).ne'
  refine ⟨⟨a,hVel,rfl⟩,?_,Or.inr ?_⟩
  · simpa only [hInv] using hv
  · simpa only [hInv] using hFar

/-- One original source-side lambda ceiling puts ALL cylinder-boundary fronts in the actual upward seed. -/
theorem exists_uniform_native_radial_seed_boundary_cover (S : KnownSideSourceData) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L : ℝ, 0 < L → ∀ C : NativeNormalCover S L,
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → lam ∈ Icc (0 : ℝ) C.dilationCeiling →
      ∀ R : ℝ, 0 < R → R < C.radiusCeiling →
      ∀ delta Rstar : ℝ, 0 < delta → 0 < Rstar → ∀ p : ℕ,
      (∀ y ∈ cylinder, referenceRadius delta Rstar p L y < R) →
      ∀ tail : ℝ, tail < Rstar*(depthPrimitive L (1/8) (1/4))^p →
      ∀ q ∈ nativeSphereFront S L C lam delta Rstar p,
        q.2 ∈ frontier cylinder → q ∈ nativeRadialSeedRoom S L C lam R tail := by
  obtain ⟨lam0,hlam0,H⟩ := exists_uniform_cylinder_boundary_seed_dichotomy S
  refine ⟨lam0,hlam0,?_⟩
  intro L hL C lam hlamPos hlamSmall hlam R hR hRoom delta Rstar hd hRs p hRadius tail hTail q hq hFrontier
  have hqN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom
    delta Rstar hd hRs p hRadius hq
  have hNorm := nativeVelocityInverse_norm_on_nativeSphereFront S L C lam hlam R hR hRoom
    delta Rstar p hd hRs hRadius q hq
  have hv : (nativeVelocityInverse S L C lam R q).2 ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hNorm];exact (referenceRadius_pos delta Rstar p L q.2 hd hRs).ne')
  refine ⟨hqN,hv,?_⟩
  rcases H lam hlamPos hlamSmall L hL delta hd Rstar hRs.le p q.2 hFrontier with hW | hFar
  · exact Or.inl hW
  · exact Or.inr (by rw [hNorm];exact hTail.trans_le hFar)

/-- Boundary coverage and openness are DISCHARGED for the actual seed, leaving one genuine compact interior room. -/
theorem exists_uniform_compact_native_radial_unseeded_center_room (S : KnownSideSourceData) :
    ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ L : ℝ, 0 < L → ∀ C : NativeNormalCover S L,
      ∀ lam : ℝ, 0 < lam → lam ≤ lam0 → lam ∈ Icc (0 : ℝ) C.dilationCeiling →
      ∀ R : ℝ, 0 < R → R < C.radiusCeiling →
      ∀ delta Rstar : ℝ, 0 < delta → 0 < Rstar → ∀ p : ℕ,
      (∀ d ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder, referenceRadius d Rstar p L y < R) →
      ∀ tail : ℝ, tail < Rstar*(depthPrimitive L (1/8) (1/4))^p →
      ∃ K : Set R3, IsCompact K ∧ K ⊆ interior cylinder ∧
        ∀ d ∈ Icc delta (1 : ℝ), ∀ q ∈ nativeSphereFront S L C lam d Rstar p,
          q ∉ nativeRadialSeedRoom S L C lam R tail → q.2 ∈ K := by
  obtain ⟨lam0,hlam0,H⟩ := exists_uniform_native_radial_seed_boundary_cover S
  refine ⟨lam0,hlam0,?_⟩
  intro L hL C lam hlamPos hlamSmall hlam R hR hRoom delta Rstar hd hRs p hRadius tail hTail
  apply exists_compact_native_unseeded_center_room S L C lam hlam delta Rstar p hd hRs
    (fun d hd' y hy => (hRadius d hd' y hy).trans hRoom)
    (nativeRadialSeedRoom S L C lam R tail)
    (isOpen_nativeRadialSeedRoom S L C lam hlam R hR hRoom tail)
  intro d hd' q hq hFrontier
  exact H L hL C lam hlamPos hlamSmall hlam R hR hRoom d Rstar (hd.trans_le hd'.1) hRs p
    (hRadius d hd') tail hTail q hq hFrontier

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
