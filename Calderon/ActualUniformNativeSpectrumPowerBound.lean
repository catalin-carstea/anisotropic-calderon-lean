import Calderon.ActualUniformNativeRestrictionApproximation
import Calderon.CountedRestrictionSpectrumPowerBound
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff Topology ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge
attribute [local instance] Classical.propDecidable
attribute [local irreducible] Regularity.classicalHarmonicL2Space harmonicRestrict

theorem exists_uniform_native_harmonicRestrict_spectrum_power_bound
    (g : Fin 2 → MatrixField) (hg : ∀ i : Fin 2, IsAdmissibleMetric (g i))
    (B : ℝ) (hB : 0 < B) (r_ext : ℝ) (hr_ext : 0 < r_ext) :
    ∃ lambda0 : ℝ, 0 < lambda0 ∧ lambda0 ≤ 1 ∧ lambda0*B < min r_ext (5/4:ℝ) ∧
      ∀ (i : Fin 2) (β : ℝ), 0 < β → ∀ d : ℝ, 0 < d →
      ∃ C0 : ℝ, 1 ≤ C0 ∧
      ∀ lambda ∈ Icc (0:ℝ) lambda0, ∀ (D : Set R3) (hD : IsOpen D), D ⊆ ball (0:R3) B →
      let A : MatrixField := principalCoefficient (fun y : R3 => g i (lambda • y))
      let hA : ContDiffOn ℝ ∞ A D := ((contDiff_principalCoefficient (g i) (hg i)).comp
        (contDiff_const_smul lambda)).contDiffOn
      ∀ (S : Set R3) (hS : IsOpen S), S.Nonempty → IsCompact (closure S) →
      (∀ x ∈ closure S, closedBall x (2*d) ⊆ D) → ∀ hSD : S ⊆ D,
      ∀ (ι : Type) (w : ι → harmonicSub D hD A hA), Orthonormal ℝ w →
      ∀ μ : ι → ℝ, (∀ j, 0 < μ j) → (∀ j, μ j ≤ 1) →
      (∀ j l, inner ℝ (harmonicRestrict D hD A hA S hSD (w j))
        (harmonicRestrict D hD A hA S hSD (w l)) = if j=l then μ j^2 else 0) →
      (∑' j, μ j^β) ≤ C0 := by
  obtain ⟨lambda0,hlambda0,hlambda01,hRoom,hApprox⟩ :=
    exists_uniform_native_harmonicRestrict_finiteRank_approximation g hg B hB r_ext hr_ext
  refine ⟨lambda0,hlambda0,hlambda01,hRoom,?_⟩
  intro i β hβ d hd
  obtain ⟨k0,hk0⟩ := exists_nat_gt (3/β)
  let k := max k0 1
  have hk : 1 ≤ k := le_max_right _ _
  have hk0le : (k0:ℝ) ≤ (k:ℝ) := by exact_mod_cast le_max_left k0 1
  have hkβ : 3 < (k:ℝ)*β := (div_lt_iff₀ hβ).mp (hk0.trans_le hk0le)
  obtain ⟨N,CE,hCE,hFinite⟩ := hApprox i k hk d hd
  obtain ⟨K0,hK0⟩ := pow_unbounded_of_one_lt CE (by norm_num : (1:ℝ)<2)
  let K := max K0 1
  have hK : 1 ≤ K := le_max_right _ _
  have hK0le : (2:ℝ)^K0 ≤ 2^K := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have hkne : k ≠ 0 := by omega
  have hBK : CE < 1*((2:ℝ)^K)^k := by
    have hP : (2:ℝ)^K ≤ ((2:ℝ)^K)^k := le_self_pow₀ (one_le_pow₀ (by norm_num)) hkne
    linarith
  let Cbound : ℝ := (N:ℝ)*8^(K+1)*(1:ℝ)^β/(1-8*(((2:ℝ)^k)⁻¹)^β)
  refine ⟨max Cbound 1,le_max_right _ _,?_⟩
  intro lambda hlambda D hD hDB A hA S hS hSne hScompact hBuffer hSD ι w hw μ hμ hμ1 hgram
  let R := harmonicRestrict D hD A hA S hSD
  have hCounted : ∀ n : ℕ, 1 ≤ n → ∃ T : harmonicSub D hD A hA →L[ℝ]
      Lp ℝ 2 ((volume:Measure R3).restrict S),
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧
      Module.finrank ℝ (LinearMap.range T.toLinearMap) ≤ N*n^3 ∧ ‖R-T‖*(n:ℝ)^k ≤ CE := by
    intro n hn
    obtain ⟨T,hTfin,hRank,hErr⟩ := hFinite lambda hlambda D hD hDB S hS hSne hScompact hBuffer hSD n hn
    have hnPos : 0 < (n:ℝ)^k := pow_pos (by exact_mod_cast (show 0<n by omega)) _
    exact ⟨T,hTfin,hRank,(le_div_iff₀ hnPos).mp hErr⟩
  exact (tsum_rpow_le_of_counted_approx R w hw μ hμ 1 (by norm_num) hμ1 hgram
    k CE N 1 hCounted β hβ hkβ K hK hBK).trans (le_max_left _ _)

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
