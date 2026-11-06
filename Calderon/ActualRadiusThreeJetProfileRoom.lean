import Calderon.ActualHigherRadiusProfile
import Calderon.ProfileRadiusJets

set_option autoImplicit false
noncomputable section
open Set
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.ActualHigherRadiusProfile
open ConformalDepth RadiusProfile ReferenceWeightedApproximation

structure ReferenceRadiusThreeJetProfileRoom (g : MatrixField) (L : ℝ) (K : Set R3) where
  radiusJetBound : ℝ
  one_le_radiusJetBound : 1 ≤ radiusJetBound
  radiusJets : ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ A : ℝ, 0 < A →
    ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ n : ℕ, n ≤ 3 →
      ‖iteratedFDeriv ℝ n (referenceRadius delta A p L) x‖ ≤
        radiusJetBound * referenceRadius delta A p L x *
          (actualReferenceBeta g L q delta A p x)^n
  threshold : ℕ
  two_le_threshold : 2 ≤ threshold
  profile : ∀ p : ℕ, threshold ≤ p → ∀ eta : ℝ, 0 < eta → eta ≤ 1 →
    ∃ A : ℝ, 0 < A ∧ ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ x ∈ K,
        1 ≤ actualReferenceBeta g L q delta A p x ∧
        referenceRadius delta A p L x*(actualReferenceBeta g L q delta A p x)^2 ≤ eta ∧
        referenceRadius delta A p L x ≤ eta

theorem exists_referenceRadiusThreeJetProfileRoom
    (g : MatrixField) (hg : IsAdmissibleMetric g) (L : ℝ) (hL : 0 < L)
    (K : Set R3) (hK : IsCompact K) :
    Nonempty (ReferenceRadiusThreeJetProfileRoom g L K) := by
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SCALAR-PROFILE BODY_ENTER"
    out.flush
  let Ck : Fin 4 → ℝ := fun k => Classical.choose
    (exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
      g hg L hL K hK k.val)
  have hCk (k : Fin 4) : 0 < Ck k :=
    (Classical.choose_spec
      (exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
        g hg L hL K hK k.val)).1
  let P : ℝ := 1 + ∑ k : Fin 4, Ck k
  have hP : 1 ≤ P := by
    have hSum : 0 ≤ ∑ k : Fin 4, Ck k :=
      Finset.sum_nonneg (fun k _ => (hCk k).le)
    dsimp [P]
    linarith
  have hCkP (k : Fin 4) : Ck k ≤ P := by
    have hSingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : Fin 4 => Ck j) (fun j _ => (hCk j).le) (Finset.mem_univ k)
    dsimp [P]
    linarith
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SCALAR-PROFILE RADIUS_CONSTANTS_READY"
    out.flush
  obtain ⟨p0,hp0Power,hp02,hProfile⟩ :=
    exists_fixed_actual_reference_beta_power_radius_profile g hg L hL K hK 2
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SCALAR-PROFILE PROFILE_PARENT_READY"
    out.flush
  have hRJets : ∀ q ∈ Icc (0 : ℝ) 1,
      ∀ delta : ℝ, 0 < delta → delta ≤ 1 → ∀ A : ℝ, 0 < A →
      ∀ p : ℕ, 1 ≤ p → ∀ x ∈ K, ∀ n : ℕ, n ≤ 3 →
        ‖iteratedFDeriv ℝ n (referenceRadius delta A p L) x‖ ≤
          P * referenceRadius delta A p L x *
            (actualReferenceBeta g L q delta A p x)^n := by
    intro q hq delta hdelta hdelta1 A hA p hp x hx n hn
    let k4 : Fin 4 := ⟨n,by omega⟩
    have hRaw := (Classical.choose_spec
      (exists_dilated_referenceRadius_fixed_uniform_radius_jet_bounds
        g hg L hL K hK k4.val)).2 q hq delta hdelta hdelta1 A hA p hp x hx
    have hRaw' : ‖iteratedFDeriv ℝ n (referenceRadius delta A p L) x‖ ≤
        Ck k4 * referenceRadius delta A p L x *
          (actualReferenceBeta g L q delta A p x)^n := by
      simpa only [Ck,k4,actualReferenceBeta] using hRaw.1
    have hRpos : 0 < referenceRadius delta A p L x :=
      referenceRadius_pos delta A p L x hdelta hA
    have hbeta0 : 0 ≤ actualReferenceBeta g L q delta A p x :=
      (actualReferenceBeta_pos g hg L q delta A p hL hdelta hA hp x).le
    exact hRaw'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCkP k4) hRpos.le) (pow_nonneg hbeta0 n))
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SCALAR-PROFILE RADIUS_JETS_READY"
    out.flush
  run_tac do
    let out ← IO.getStdout
    out.putStrLn "LA-SCALAR-PROFILE ASSEMBLY_ENTER"
    out.flush
  exact ⟨{ radiusJetBound := P
           one_le_radiusJetBound := hP
           radiusJets := hRJets
           threshold := p0
           two_le_threshold := hp02
           profile := hProfile }⟩

end OAI.AnisotropicCalderon.ActualHigherRadiusProfile
