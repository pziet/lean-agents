import os
import pytest

from agent_harness.lean_interface import LeanInterface

def test_lean_interface_basic(tmp_path):
    lean_root = tmp_path / "lean"
    file_dir = "test_dir"
    li = LeanInterface(str(lean_root), file_dir)

    # Directories should be created
    stubs_dir = lean_root / file_dir / "stubs"
    proven_dir = lean_root / file_dir / "proven"
    attempts_dir = lean_root / file_dir / "attempts"
    assert stubs_dir.exists() and stubs_dir.is_dir()
    assert proven_dir.exists() and proven_dir.is_dir()
    assert attempts_dir.exists() and attempts_dir.is_dir()

    # No lemmas initially
    assert li.get_available_lemmas() == []

    # Create a stub file and test availability
    stub_file = stubs_dir / "lemma1.lean"
    stub_content = "def lemma1 := 1"
    stub_file.write_text(stub_content)
    available = li.get_available_lemmas()
    assert isinstance(available, list) and available == ["lemma1"]

    # get_file returns correct content
    content = li.get_file("lemma1", "stubs")
    assert content == stub_content

    # create_attempt_file and delete_attempt_file
    attempt_path = li.create_attempt_file("proof code", "lemma1", "agentX")
    assert os.path.exists(attempt_path)
    li.delete_attempt_file(attempt_path)
    assert not os.path.exists(attempt_path)

    # save_proven_lemma writes file
    proof_script = "proof code"
    proven_path = li.save_proven_lemma("lemma1", proof_script)
    assert proven_path is not None and os.path.exists(proven_path)

    # duplicate save returns None
    duplicate = li.save_proven_lemma("lemma1", proof_script)
    assert duplicate is None

    # After proving, lemma should not be available
    assert li.get_available_lemmas() == []

    # delete_proven_lemmas removes files
    li.delete_proven_lemmas()
    assert list(proven_dir.iterdir()) == []
