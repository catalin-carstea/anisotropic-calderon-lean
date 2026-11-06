import Calderon.ActualFiniteCoverCoercivityScalar
import Calderon.ActualFinitePhysicalAdjointOutput
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped Topology BigOperators
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask.TransferPhysicalCoercivity
open DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open MainPhysicalCoercivityAssembly

/-- Gather the exact seven positive packet thresholds before choosing profiles.
The finite packet index type need not be inhabited. -/
theorem exists_packet_eta_target
    {ι : Type*} [Fintype ι] (epsMax : ℝ) (hepsMax : 0 < epsMax)
    (dP etaI etaF etaTS etaUS etaGraph etaAbs : ι → ℝ)
    (hP : ∀ i, 0 < dP i) (hI : ∀ i, 0 < etaI i)
    (hF : ∀ i, 0 < etaF i) (hTS : ∀ i, 0 < etaTS i)
    (hUS : ∀ i, 0 < etaUS i) (hGraph : ∀ i, 0 < etaGraph i)
    (hAbs : ∀ i, 0 < etaAbs i) :
    ∃ etaTarget : ℝ, 0 < etaTarget ∧ etaTarget ≤ 1 ∧ etaTarget ≤ epsMax ∧
      ∀ i, etaTarget ≤ dP i / 2 ∧ etaTarget ≤ etaI i ∧ etaTarget ≤ etaF i ∧
        etaTarget ≤ etaTS i ∧ etaTarget ≤ etaUS i ∧ etaTarget ≤ etaGraph i ∧
        etaTarget ≤ etaAbs i := by
  let packet : ι → ℝ := fun i => min (dP i / 2)
    (min (etaI i) (min (etaF i) (min (etaTS i) (min (etaUS i) (min (etaGraph i) (etaAbs i))))))
  have hp (i : ι) : 0 < packet i :=
    lt_min (div_pos (hP i) (by norm_num))
      (lt_min (hI i) (lt_min (hF i)
        (lt_min (hTS i) (lt_min (hUS i) (lt_min (hGraph i) (hAbs i))))))
  obtain ⟨etaAll, hAllPos, hAllOne, hAll⟩ := exists_pos_le_one_and_forall_le packet hp
  refine ⟨min epsMax etaAll, lt_min hepsMax hAllPos,
    (min_le_right _ _).trans hAllOne, min_le_left _ _, ?_⟩
  intro i
  have hi : min epsMax etaAll ≤ packet i := (min_le_right _ _).trans (hAll i)
  simpa only [packet, le_min_iff] using hi

/-- Two full physical fields with the same forward negative graph on a set
containing both supports agree everywhere. No finite output is required. -/
theorem eq_of_physicalL2Inclusion_eq_on_common_tsupport
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
    (W Y : R3 → SphereL2) (K : Set R3)
    (hW : tsupport W ⊆ K) (hY : tsupport Y ⊆ K)
    (h : ∀ x ∈ K, MainPhysicalGraphBridge.physicalL2Inclusion hO hD (W x) =
      MainPhysicalGraphBridge.physicalL2Inclusion hO hD (Y x)) :
    W = Y := by
  funext x
  by_cases hx : x ∈ K
  · apply (sphereSobolevZeroEquiv hO hD).injective
    apply sphereSobolevInclusionL_injective 0 (-(1/2 : ℝ)) (by norm_num)
    exact h x hx
  · have hw : W x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hW hs))
    have hy : Y x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hx (hY hs))
    exact hw.trans hy.symm

/-- Close the finite cover and compare the original weighted input norm with
the profile energy. The comparison is needed only on the input support. -/
theorem weighted_finite_cover_norm_le_of_local_energy
    (N : ℕ) (mu E : R3 → ℝ) (A V : R3 → SphereL2)
    (Ei : Fin N → R3 → ℝ) (Wi : Fin N → R3 → SphereL2)
    (Q cRaise BF : ℝ)
    (hmu : ∀ x, 0 ≤ mu x) (hE : ∀ x, 0 ≤ E x)
    (hQ : 0 ≤ Q) (hc : 0 < cRaise)
    (hAInt : Integrable (fun x => mu x * ‖A x‖^2))
    (hEInt : Integrable (fun x => mu x * E x))
    (hInput : ∀ x ∈ tsupport A, ‖A x‖^2 ≤ E x)
    (hFloor : 1 + 32 * (max 1 (N : ℝ))^2 * Q / cRaise ≤ BF)
    (hEnergy : (∫ x, mu x * E x) ≤
      (N : ℝ) * ∑ i : Fin N, ∫ x, mu x * Ei i x)
    (hLocal : ∀ i : Fin N, (cRaise / 8) * (∫ x, mu x * Ei i x) ≤
      ∫ x, mu x * ‖Wi i x‖^2)
    (hOutput : (∑ i : Fin N, ∫ x, mu x * ‖Wi i x‖^2) ≤
      2 * (∫ x, mu x * ‖V x‖^2) + (2 * (N : ℝ) * Q / BF) * (∫ x, mu x * E x)) :
    0 < cRaise / (32 * max 1 (N : ℝ)) ∧
      (cRaise / (32 * max 1 (N : ℝ))) * (∫ x, mu x * ‖A x‖^2) ≤
        ∫ x, mu x * ‖V x‖^2 := by
  have hIE : 0 ≤ ∫ x, mu x * E x := integral_nonneg (fun x => mul_nonneg (hmu x) (hE x))
  have hIV : 0 ≤ ∫ x, mu x * ‖V x‖^2 := integral_nonneg (fun x => mul_nonneg (hmu x) (sq_nonneg _))
  have hSum : (cRaise / 8) * (∑ i : Fin N, ∫ x, mu x * Ei i x) ≤
      ∑ i : Fin N, ∫ x, mu x * ‖Wi i x‖^2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hLocal i)
  obtain ⟨hc', hEnergyBound⟩ := finite_cover_scalar_coercivity (N : ℝ) Q cRaise BF
    (∫ x, mu x * E x) (∫ x, mu x * ‖V x‖^2)
    (∑ i : Fin N, ∫ x, mu x * Ei i x) (∑ i : Fin N, ∫ x, mu x * ‖Wi i x‖^2)
    (Nat.cast_nonneg N) hQ hc hIE hIV hFloor hEnergy hSum hOutput
  have hPoint (x : R3) : mu x * ‖A x‖^2 ≤ mu x * E x := by
    apply mul_le_mul_of_nonneg_left _ (hmu x)
    by_cases hx : x ∈ tsupport A
    · exact hInput x hx
    · have hz : A x = 0 := image_eq_zero_of_notMem_tsupport hx
      simpa only [hz, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0)] using hE x
  have hInt := integral_mono hAInt hEInt hPoint
  exact ⟨hc', (mul_le_mul_of_nonneg_left hInt hc'.le).trans hEnergyBound⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask.TransferPhysicalCoercivity
