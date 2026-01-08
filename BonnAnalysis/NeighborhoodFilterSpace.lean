import Mathlib.Topology.Sequences
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.Order
import Mathlib.Order.Filter.Basic
import BonnAnalysis.ConvergingSequences
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Topology.UniformSpace.UniformConvergence
open Order Set Filter
open Filter
open scoped Topology

universe u
class NeighborhoodFilterSpace (X : Type u) where
  nbh : X → Filter X
  nbh_rfl : ∀ x , ∀ N ∈ nbh x , x ∈ N
  nbh_interior : ∀ x : X , ∀ N ∈ nbh x ,  { z ∈ N | N ∈ nbh z} ∈ nbh x
open NeighborhoodFilterSpace
variable {X : Type u} [NeighborhoodFilterSpace X]
instance topFromNbh  : TopologicalSpace X where
  IsOpen A := ∀ x ∈ A , A ∈ nbh x
  isOpen_univ := fun x _ => (nbh x).univ_sets
  isOpen_inter := fun U V hU hV x hx => by
    apply (nbh x).inter_sets
    exact hU x hx.1
    exact hV x hx.2

  isOpen_sUnion := fun U ass => by
    intro x hx
    obtain ⟨ Ui , hUi ⟩ := hx
    apply (nbh x).sets_of_superset (ass _ hUi.1 _ hUi.2)
    rw [@subset_def]
    intro x hx
    use Ui
    exact ⟨ hUi.1 , hx⟩

lemma lemmaNbhd

   : ∀ x : X , nhds x = nbh x := by -- @nhds _ (fromConvSeq seq) = nbh seq := by
  --funext x
  intro x

  rw [le_antisymm_iff]
  constructor
  · rw [le_def]
    intro A hA
    rw [mem_nhds_iff]
    use {a ∈ A | A  ∈ nbh a}
    constructor
    · simp
    · constructor
      · rw [IsOpen]
        intro _ hx
        apply nbh_interior
        exact hx.2
      · constructor
        · apply nbh_rfl ; exact hA
        · assumption
  · rw [@le_nhds_iff]
    intro s hxs hs
    exact hs x hxs
open MaesureTheory
open ConvergingSequences
instance {X : Type u} [ConvergingSequences X]: NeighborhoodFilterSpace X  where
  nbh := nbh
  nbh_rfl := fun x N hN => by
    specialize hN _ (seq_cnst x)
    exact (seqInNhd hN).choose_spec
  nbh_interior := fun x N hN => by
    intro a (ha : a ⟶ x)
    by_contra φ
    have φ' : {z | N ∈ MaesureTheory.nbh z} ∉ map a atTop := by
      by_contra φ'
      apply φ
      apply inter_sets
      · exact hN _ ha
      · exact φ'
    obtain ⟨ a' , ha'⟩  := subSeqCnstrction φ'
    have hN' : ∀ n , N ∉ nbh (a' n) := ha'
    simp at hN'
    have hN' : ∀ n , ∃ bn , (bn ⟶ a' n) ∧ (N ∉ map bn atTop) :=  by simp ; exact hN'
    have hN' : ∀ n , ∃ bn , (bn ⟶ a' n) ∧ (∀ m , bn m ∉ N) := fun n => by
      obtain ⟨ bn' , hbn' ⟩ := subSeqCnstrction (hN' n).choose_spec.2
      use bn'
      constructor
      · apply seq_sub
        exact (hN' n).choose_spec.1
      · exact hbn'
    let b : ℕ → ℕ → X := fun n => (hN' n).choose
    sorry
    -- have hb : (fun n => b n n) ⟶ x := by

    --   apply seq_diag (seq_sub ha a')
    --   intro n
    --   exact (hN' n).choose_spec.1
    -- specialize hN _ hb
    -- obtain ⟨ n , hn⟩ := seqInNhd hN
    -- apply (hN' n).choose_spec.2 n hn
