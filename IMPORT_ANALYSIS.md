# Import System Analysis and Implementation Plan

## Current State Analysis

### How Imports Work Currently

The import resolution is handled in `aeon/sugar/desugar.py` in the `_resolve_import()` function (line 1425-1449).

**Current search path precedence:**
1. Current working directory (`Path.cwd()`)
2. Current working directory + `/libraries` subdirectory (`Path.cwd() / "libraries"`)
3. Directories from the `AEONPATH` environment variable (semicolon-separated)

**Code snippet:**
```python
def _resolve_import(imp: ImportAe) -> Program:
    path = imp.file_path
    possible_containers = (
        [Path.cwd()] + [Path.cwd() / "libraries"] + [Path(s) for s in os.environ.get("AEONPATH", ";").split(";") if s]
    )
    for container in possible_containers:
        file = container / f"{path}"
        if file.exists():
            # ... parse and cache
```

### Problem Statement

When running `python -m aeon /some/random/file.ae` from anywhere in the filesystem:

❌ **Does NOT work:** Importing standard library modules like `List`, `Math`, etc.
- The search only looks in `/some/random/` and `/some/random/libraries/`
- The installed aeon package's `libraries/` directory is never checked

✅ **Works:** Importing relative files in the same directory
- Files in the same directory as the input file can be imported

### Testing Results

```bash
$ cd /tmp
$ cat > test_import.ae << 'EOF'
import List;

def main : Int = 42;
EOF

$ python3 -m aeon test_import.ae
>>> Error at FileLocation(file='test_import.ae', start=(1, 1), end=(1, 13)):
Could not find module 'List' (file: List.ae) in the following list of container folders: [PosixPath('/tmp'), PosixPath('/tmp/libraries')]
```

## Design Plan

### Goal

Enable users to:
1. Run aeon on any `.ae` file anywhere in the filesystem
2. Import standard library modules (List, Math, etc.) from the installed aeon package
3. Import relative files from the same directory
4. Optionally use `AEONPATH` for custom library directories

### Solution Design

#### Option 1: Add Package Libraries to Search Path (RECOMMENDED)

**Approach:** Modify `_resolve_import()` to include the installed package's `libraries/` directory in the search path.

**Search path order:**
1. Current working directory (for relative imports from script location)
2. `cwd/libraries` (backward compatibility)
3. **[NEW]** Package installation `libraries/` directory
4. `AEONPATH` directories (user-defined override paths)

**Implementation:**
```python
import aeon
import os
from pathlib import Path

def _get_package_libraries_dir() -> Path | None:
    """Return the path to the libraries directory in the installed aeon package."""
    try:
        aeon_package_dir = Path(aeon.__file__).parent.parent
        libraries_dir = aeon_package_dir / "libraries"
        if libraries_dir.exists() and libraries_dir.is_dir():
            return libraries_dir
    except Exception:
        pass
    return None

def _resolve_import(imp: ImportAe) -> Program:
    path = imp.file_path
    
    possible_containers = [Path.cwd(), Path.cwd() / "libraries"]
    
    # Add package libraries directory
    pkg_libs = _get_package_libraries_dir()
    if pkg_libs:
        possible_containers.append(pkg_libs)
    
    # Add AEONPATH directories
    aeonpath = os.environ.get("AEONPATH", "")
    if aeonpath:
        possible_containers.extend([Path(s) for s in aeonpath.split(";") if s])
    
    for container in possible_containers:
        file = container / path
        if file.exists():
            # ... existing logic
```

**Pros:**
- Minimal code changes
- Backward compatible
- Works immediately with editable installs (`pip install -e .`)
- No packaging changes needed

**Cons:**
- Relies on libraries being in the repo structure (not packaged)
- Won't work with wheel installations unless libraries are included

#### Option 2: Package Libraries in the Distribution

**Approach:** Include the `libraries/` directory in the Python package distribution.

**Changes needed:**

1. **Update `pyproject.toml`:**
```toml
[tool.setuptools]
include-package-data = true

[tool.setuptools.packages.find]
include = ["aeon*", "libraries"]

[tool.setuptools.package-data]
aeon = ["**/*.lark"]
"" = ["libraries/*.ae"]  # Include libraries at package root
```

OR move libraries inside the aeon package:
```
aeon/
  libraries/
    List.ae
    Math.ae
    ...
```

2. **Update import resolution to use `importlib.resources` or `pkg_resources`:**
```python
from importlib import resources

def _get_package_libraries_dir() -> Path:
    """Return path to packaged libraries."""
    try:
        if sys.version_info >= (3, 9):
            return resources.files("aeon") / "libraries"
        else:
            # Fallback for older Python
            import pkg_resources
            return Path(pkg_resources.resource_filename("aeon", "libraries"))
    except Exception:
        # Fallback to relative path
        return Path(__file__).parent.parent / "libraries"
```

**Pros:**
- Works with wheel installations
- Libraries are truly part of the package
- Cleaner distribution

**Cons:**
- More invasive changes
- Requires packaging restructure
- Need to test wheel building

#### Option 3: Use AEONPATH by Default

**Approach:** Document that users must set `AEONPATH` to point to the libraries.

**Implementation:**
- Document in README/installation guide
- Possibly set `AEONPATH` during installation

**Pros:**
- No code changes

**Cons:**
- Poor user experience
- Extra setup step for every user
- Not cross-platform friendly

### Recommended Approach

**Implement Option 1 first** (add package libraries to search path) because:
1. Works immediately with current setup
2. Minimal risk
3. Backward compatible
4. Can be enhanced with Option 2 later

**Then consider Option 2** for proper packaging in a future PR.

## Implementation Steps

### Phase 1: Fix Immediate Issue (This PR)

1. ✅ Analyze current import system
2. Create `_get_package_libraries_dir()` helper function
3. Modify `_resolve_import()` to include package libraries in search path
4. Add tests:
   - Test importing std library from outside project directory
   - Test relative imports still work
   - Test AEONPATH override still works
5. Update documentation in `CLAUDE.md` and `README.md`

### Phase 2: Proper Packaging (Future PR)

1. Move `libraries/` inside `aeon/` package
2. Update `pyproject.toml` to include library files
3. Update import resolution to use `importlib.resources`
4. Test wheel distribution
5. Update CI/CD for package verification

## Testing Strategy

### Manual Tests

```bash
# Test 1: Import std library from /tmp
cd /tmp
cat > test.ae << 'EOF'
import List;
def main : Int = 42;
EOF
python -m aeon test.ae  # Should succeed

# Test 2: Import relative file
cd /tmp
cat > helper.ae << 'EOF'
def helper : Int = 42;
EOF
cat > main.ae << 'EOF'
import helper;
def main : Int = helper.helper;
EOF
python -m aeon main.ae  # Should succeed

# Test 3: AEONPATH override
mkdir /tmp/custom_libs
cat > /tmp/custom_libs/Custom.ae << 'EOF'
def custom : Int = 99;
EOF
cat > /tmp/test_aeonpath.ae << 'EOF'
import Custom;
def main : Int = Custom.custom;
EOF
AEONPATH="/tmp/custom_libs" python -m aeon /tmp/test_aeonpath.ae  # Should succeed
```

### Unit Tests

Create `tests/test_imports.py`:
- Test `_get_package_libraries_dir()` returns valid path
- Test import resolution order
- Test AEONPATH parsing
- Test relative imports
- Test standard library imports

## Files to Modify

1. `aeon/sugar/desugar.py` - Update `_resolve_import()`
2. `tests/test_imports.py` - New test file
3. `CLAUDE.md` - Document import behavior
4. `README.md` - User documentation

## Backward Compatibility

All existing code will continue to work:
- Projects with `libraries/` subdirectory: ✅ Works (searched first)
- Projects using `AEONPATH`: ✅ Works (still respected)
- Projects in aeon repo: ✅ Works (cwd/libraries found first)

## Edge Cases

1. **Shadowing:** If user has `./libraries/List.ae`, it takes precedence over package `List.ae` ✅ Good
2. **No package installation:** Falls back gracefully (cwd and AEONPATH only) ✅ Good
3. **Circular imports:** Already handled by `_currently_importing` set ✅ Good
4. **Import caching:** Already handled by `_import_cache` dict ✅ Good
