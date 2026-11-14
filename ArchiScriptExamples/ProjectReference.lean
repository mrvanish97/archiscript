import ArchiScript.Partition

/-! Stage 2 project-reference semantics over an explicit symbolic interpretation
of URI and filesystem observations. These fields are not preclassified success/
failure constructors. Coverage concerns every observation in this carrier.
The correspondence of these observations to real URI parsing and filesystem
state is an external boundary assumption, not a theorem of this example. -/
namespace ArchiScriptExamples.ProjectReference
open ArchiScript

structure Uri where
  path : String
  scheme : String
  filename : String
  directory : Bool
  packagePresent : Bool
  indexPresent : Bool

private def sample (scheme filename : String) (directory packagePresent indexPresent : Bool) : Uri :=
  ⟨"/symbolic-uri", scheme, filename, directory, packagePresent, indexPresent⟩

def uri : Subdomain Uri :=
  .root "Uri" (fun _ => True) ⟨sample "https" "x" false false false, trivial⟩ (.predicate _)

def fileUri : Subdomain Uri :=
  .child "FileUri" uri (fun x => x.scheme = "file")
    ⟨sample "file" "x" false false false, by dsimp [uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def unsupportedScheme : Subdomain Uri :=
  .remainder "UnsupportedUriScheme" uri fileUri fileUri.contained
    ⟨sample "https" "x" false false false, by dsimp [fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitFileUri : SemanticSplit uri :=
  .complement uri fileUri fileUri.contained "UnsupportedUriScheme" unsupportedScheme.nonempty

def dirUri : Subdomain Uri :=
  .child "DirUri" fileUri (fun x => x.directory = true)
    ⟨sample "file" "x" true false false, by dsimp [unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def nonDirUri : Subdomain Uri :=
  .remainder "NonDirFileUri" fileUri dirUri dirUri.contained
    ⟨sample "file" "x" false false false, by dsimp [dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitDirUri : SemanticSplit fileUri :=
  .complement fileUri dirUri dirUri.contained "NonDirFileUri" nonDirUri.nonempty

def packageUri : Subdomain Uri :=
  .child "PackageJsonUri" nonDirUri (fun x => x.filename = "package.json")
    ⟨sample "file" "package.json" false false false, by dsimp [nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def nonPackageUri : Subdomain Uri :=
  .remainder "NonPackageJsonFileUri" nonDirUri packageUri packageUri.contained
    ⟨sample "file" "x" false false false, by dsimp [packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitPackageUri : SemanticSplit nonDirUri :=
  .complement nonDirUri packageUri packageUri.contained "NonPackageJsonFileUri" nonPackageUri.nonempty

def indexUri : Subdomain Uri :=
  .child "IndexArchiTsUri" nonPackageUri (fun x => x.filename = "index.archi.ts")
    ⟨sample "file" "index.archi.ts" false false false, by dsimp [nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def unsupportedFile : Subdomain Uri :=
  .remainder "UnsupportedArchiScriptProjectFileUri" nonPackageUri indexUri indexUri.contained
    ⟨sample "file" "other.ts" false false false, by dsimp [indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitIndexUri : SemanticSplit nonPackageUri :=
  .complement nonPackageUri indexUri indexUri.contained "UnsupportedArchiScriptProjectFileUri" unsupportedFile.nonempty

def dirComplete : Subdomain Uri :=
  .child "DirUriWithPackageJsonAndIndex" dirUri (fun x => x.packagePresent = true ∧ x.indexPresent = true)
    ⟨sample "file" "dir" true true true, by dsimp [unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def dirMissing : Subdomain Uri :=
  .remainder "DirUriMissingPackageJsonOrIndex" dirUri dirComplete dirComplete.contained
    ⟨sample "file" "dir" true false true, by dsimp [dirComplete, unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitDirComplete : SemanticSplit dirUri :=
  .complement dirUri dirComplete dirComplete.contained "DirUriMissingPackageJsonOrIndex" dirMissing.nonempty

def packageComplete : Subdomain Uri :=
  .child "PackageJsonUriWithIndexSibling" packageUri (fun x => x.indexPresent = true)
    ⟨sample "file" "package.json" false true true, by dsimp [dirMissing, dirComplete, unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def packageMissing : Subdomain Uri :=
  .remainder "PackageJsonUriWithoutIndexSibling" packageUri packageComplete packageComplete.contained
    ⟨sample "file" "package.json" false true false, by dsimp [packageComplete, dirMissing, dirComplete, unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitPackageComplete : SemanticSplit packageUri :=
  .complement packageUri packageComplete packageComplete.contained "PackageJsonUriWithoutIndexSibling" packageMissing.nonempty

def indexComplete : Subdomain Uri :=
  .child "IndexUriWithPackageJsonSibling" indexUri (fun x => x.packagePresent = true)
    ⟨sample "file" "index.archi.ts" false true true, by dsimp [packageMissing, packageComplete, dirMissing, dirComplete, unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def indexMissing : Subdomain Uri :=
  .remainder "IndexUriWithoutPackageJsonSibling" indexUri indexComplete indexComplete.contained
    ⟨sample "file" "index.archi.ts" false false true, by dsimp [indexComplete, packageMissing, packageComplete, dirMissing, dirComplete, unsupportedFile, indexUri, nonPackageUri, packageUri, nonDirUri, dirUri, unsupportedScheme, fileUri, uri, Subdomain.child, Subdomain.root, Subdomain.remainder, Domain.relativeComplement, sample]; decide⟩

def splitIndexComplete : SemanticSplit indexUri :=
  .complement indexUri indexComplete indexComplete.contained "IndexUriWithoutPackageJsonSibling" indexMissing.nonempty

def nonPackageTree : SemanticSplit nonPackageUri :=
  splitIndexUri.refine fun
    | false => .singleton unsupportedFile
    | true => splitIndexComplete

def nonDirTree : SemanticSplit nonDirUri :=
  splitPackageUri.refine fun
    | false => nonPackageTree
    | true => splitPackageComplete

def fileTree : SemanticSplit fileUri :=
  splitDirUri.refine fun
    | false => nonDirTree
    | true => splitDirComplete

def referenceTree : SemanticSplit uri :=
  splitFileUri.refine fun
    | false => .singleton unsupportedScheme
    | true => fileTree

abbrev projectReference : VDP := Partition.ofSplit referenceTree (fun _ => trivial)

/-- All eight success and failure leaves partition every symbolic URI. -/
theorem reference_complete (x : Uri) : ∃ i, projectReference.member i x :=
  projectReference.coverage x

theorem reference_disjoint {i j : projectReference.MemberIndex} (different : i ≠ j) (x : Uri) :
    ¬ (projectReference.member i x ∧ projectReference.member j x) :=
  projectReference.disjoint different x

#guard referenceTree.indices.length == 8
#guard (referenceTree.indices.map fun i => (referenceTree.children i).name) ==
  ["UnsupportedUriScheme", "UnsupportedArchiScriptProjectFileUri",
   "IndexUriWithoutPackageJsonSibling", "IndexUriWithPackageJsonSibling",
   "PackageJsonUriWithoutIndexSibling", "PackageJsonUriWithIndexSibling",
   "DirUriMissingPackageJsonOrIndex", "DirUriWithPackageJsonAndIndex"]

/-- Successes cannot replace the actual Uri boundary: an unsupported scheme
is a concrete counterexample before any operation is analyzed. -/
theorem successes_do_not_cover : ¬ (∀ x : Uri,
    dirComplete.meaning x ∨ packageComplete.meaning x ∨ indexComplete.meaning x) := by
  intro h
  have bad := h (sample "https" "other.ts" false false false)
  dsimp [dirComplete, packageComplete, indexComplete, indexUri, nonPackageUri,
    packageUri, nonDirUri, dirUri, fileUri, uri, Subdomain.child, Subdomain.remainder,
    Subdomain.root, Domain.relativeComplement, sample] at bad
  simp at bad

end ArchiScriptExamples.ProjectReference
