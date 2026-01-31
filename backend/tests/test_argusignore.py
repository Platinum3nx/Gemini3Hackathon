import unittest
import os
import shutil
import tempfile
import sys

# Add project root to path
sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), "../..")))

from backend import repo_manager

class TestArgusIgnore(unittest.TestCase):
    def setUp(self):
        # Create a temporary directory for the mock repo
        self.test_dir = tempfile.mkdtemp()
        
        # Create standard file structure
        # repo/
        #   - main.py
        #   - legacy.py
        #   - utils.py
        #   - tests/
        #       - test_main.py (should be ignored by standard logic)
        #   - legacy_module/
        #       - old_stuff.py
        #   - deep/
        #       - generated.py
        #       - real_code.py
        
        self.create_file("main.py")
        self.create_file("legacy.py")
        self.create_file("utils.py")
        
        os.makedirs(os.path.join(self.test_dir, "tests"))
        self.create_file("tests/test_main.py")
        
        os.makedirs(os.path.join(self.test_dir, "legacy_module"))
        self.create_file("legacy_module/old_stuff.py")
        
        os.makedirs(os.path.join(self.test_dir, "deep"))
        self.create_file("deep/generated.py")
        self.create_file("deep/real_code.py")

    def tearDown(self):
        shutil.rmtree(self.test_dir)

    def create_file(self, rel_path, content=""):
        full_path = os.path.join(self.test_dir, rel_path)
        with open(full_path, 'w') as f:
            f.write(content)

    def create_argusignore(self, content):
        with open(os.path.join(self.test_dir, ".argusignore"), 'w') as f:
            f.write(content)

    def test_no_argusignore(self):
        """Test file collection works normally without .argusignore"""
        files = repo_manager.get_all_python_files(self.test_dir)
        
        # Standard ignores (tests/) should still apply
        self.assertNotIn("tests/test_main.py", files)
        
        # All other files should be present
        self.assertIn("main.py", files)
        self.assertIn("legacy.py", files)
        self.assertIn("utils.py", files)
        self.assertIn("legacy_module/old_stuff.py", files)
        self.assertIn("deep/generated.py", files)
        self.assertIn("deep/real_code.py", files)

    def test_simple_ignore(self):
        """Test ignoring specific files"""
        self.create_argusignore("legacy.py\n")
        files = repo_manager.get_all_python_files(self.test_dir)
        
        self.assertNotIn("legacy.py", files)
        self.assertIn("main.py", files)

    def test_wildcard_ignore(self):
        """Test wildcard ignores"""
        self.create_argusignore("*.py\n!main.py") # Ignore all py, keep main.py
        # Note: Negation support depends on gitwildmatch. verify if it works, or stick to simple wildcard
        
        # Let's test simple wildcard first
        self.create_argusignore("*generated.py\n")
        files = repo_manager.get_all_python_files(self.test_dir)
        
        self.assertNotIn("deep/generated.py", files)
        self.assertIn("deep/real_code.py", files)

    def test_directory_ignore(self):
        """Test directory ignores"""
        self.create_argusignore("legacy_module/")
        files = repo_manager.get_all_python_files(self.test_dir)
        
        self.assertNotIn("legacy_module/old_stuff.py", files)
        self.assertIn("main.py", files)

    def test_comments_and_empty_lines(self):
        """Test robustness of parsing"""
        content = """
        # This is a comment
        
        legacy.py
        
        # Another comment
        """
        self.create_argusignore(content)
        files = repo_manager.get_all_python_files(self.test_dir)
        
        self.assertNotIn("legacy.py", files)
        self.assertIn("main.py", files)

if __name__ == "__main__":
    unittest.main()
