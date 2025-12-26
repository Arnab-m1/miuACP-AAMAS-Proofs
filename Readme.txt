muACP Supplementary Materials
=============================

This archive provides the mechanized artifacts referenced in the paper:

"μACP: A Formal Calculus for Expressive, Resource-Constrained Agent Communication"

Contents
--------
- muACP_Fixed.tla   : TLA+ specification of μACP operational semantics
- muACP_Fixed.cfg   : TLC configuration file for model checking
- muACP.v           : Coq development for resource and consensus proofs

Requirements
------------
- TLA+ Tools (TLC model checker), version ≥ 2.16
- Coq ≥ 8.17 (tested with Coq 8.17.1)
- Standard Coq tactics (`auto`, `lia`) are sufficient; no external libraries required
- Java 17+ (for TLC)

Installation Options
--------------------
**Option 1: Docker (Recommended for Reproducibility)**
  
  **Using Docker Compose (easiest):**
  ```bash
  docker-compose up -d
  docker-compose exec muacp-verification bash
  ```
  
  **Using Docker directly:**
  1. Build the Docker image:
     ```bash
     docker build -t muacp-verification .
     ```
  2. Run the container with the project mounted:
     ```bash
     docker run -it -v $(pwd):/workspace muacp-verification
     ```
  
  3. Inside the container, verify installations:
     ```bash
     eval $(opam env)  # Initialize opam environment
     coqc --version    # Should show Coq 8.17.1
     java -version     # Should show Java 17+
     ```
  
  4. Run verifications as described in the Usage section below.

**Option 2: Manual Installation**
  - **TLA+ Tools**: Download from https://github.com/tlaplus/tlaplus/releases
    - Extract TLA+ Toolbox or use tla2tools.jar directly
    - Ensure Java 17+ is installed
  - **Coq**: Install via opam (OCaml package manager)
    ```bash
    opam init
    opam repo add coq-released https://coq.inria.fr/opam/released
    opam install coq.8.17.1
    eval $(opam env)
    ```

**Option 3: Google Colab (Cloud-based, No Local Installation)**

  Google Colab provides a free cloud environment that can run both TLA+ and Coq verification.
  
  **Setup in Colab:**
  
  1. Create a new Colab notebook: https://colab.research.google.com/
  
  2. Upload the project files (`muACP_Fixed.tla`, `muACP_Fixed.cfg`, `muACP.v`) to Colab:
     - Use the file upload icon in the left sidebar, or
     - Mount Google Drive and copy files there
  
  3. Install dependencies (run in Colab cells):
  
     ```python
     # Cell 1: Install system dependencies and Java
     !apt-get update -qq
     !apt-get install -y -qq openjdk-17-jdk wget
     
     # Cell 2: Install Coq via opam
     !apt-get install -y -qq opam pkg-config libgmp-dev libnum-ocaml-dev
     !opam init --disable-sandboxing -y
     !eval $(opam env) && opam repo add coq-released https://coq.inria.fr/opam/released
     !eval $(opam env) && opam install -y coq.8.17.1
     
     # Note: Coq installation may take 10-15 minutes. Be patient!
     
     # Cell 3: Download TLA+ Tools
     !mkdir -p /opt/tla
     !wget -q https://github.com/tlaplus/tlaplus/releases/download/v1.8.0/tla2tools.jar -O /opt/tla/tla2tools.jar
     
     # Cell 4: Verify installations
     !java -version
     !eval $(opam env) && coqc --version
     ```
  
  4. Run TLA+ verification:
     ```python
     # Run TLC model checker
     !java -cp /opt/tla/tla2tools.jar tlc2.TLC -config muACP_Fixed.cfg muACP_Fixed.tla
     ```
  
  5. Run Coq verification:
     ```python
     # Compile and verify Coq development
     !eval $(opam env) && coqc muACP.v
     ```
  
  **Important Notes:**
  - Colab sessions are temporary. For persistent storage, mount Google Drive and save files there.
  - The opam environment needs to be re-initialized in each new Colab session with `eval $(opam env)`.
  - Coq installation via opam takes approximately 10-15 minutes. Please be patient during setup.
  - If you encounter issues with opam, ensure all cells are run in order and wait for each to complete.

**Version Manifest**
  - See `versions.txt` for exact version requirements and installation notes.

Usage
-----
1. **TLA+ / TLC**
   
   **In Docker:**
   ```bash
   # Ensure opam environment is initialized
   eval $(opam env)
   
   # Run TLC model checker
   java -cp /opt/tla/tla2tools.jar tlc2.TLC -config muACP_Fixed.cfg muACP_Fixed.tla
   ```
   
   **In Google Colab:**
   ```python
   # Run TLC model checker
   !java -cp /opt/tla/tla2tools.jar tlc2.TLC -config muACP_Fixed.cfg muACP_Fixed.tla
   ```
   
   **Local installation:**
   - Open `muACP_Fixed.tla` in the TLA+ Toolbox or run with TLC.
   - Use the supplied configuration `muACP_Fixed.cfg`.
   - Command-line: `tlc -config muACP_Fixed.cfg muACP_Fixed.tla`
   
   **Model details:**
   - The model explores systems of 3–7 agents with lossy/duplicating channels.
   - Verified invariants:
     * Resource counters never negative
     * Headers fixed at 64 bits; verbs ∈ {PING, TELL, ASK, OBSERVE}
     * Eventual delivery under partial synchrony (stable channels)

2. **Coq proofs**
   
   **In Docker:**
   ```bash
   # Initialize opam environment
   eval $(opam env)
   
   # Compile and verify the Coq development
   coqc muACP.v
   ```
   
   **In Google Colab:**
   ```python
   # Initialize opam environment and compile Coq development
   !eval $(opam env) && coqc muACP.v
   ```
   
   **Local installation:**
   - Load `muACP.v` in CoqIDE or Proof General.
   - Run `coqc muACP.v` to check all lemmas.
   
   **Verified theorems:**
   - Resource boundedness: counters remain non-negative
   - Consensus safety: at most one value chosen under crash faults
   - ~85% of proof obligations discharged automatically.
   - No `Admitted.` statements remain; all proofs complete.

Notes
-----
- The artifacts correspond to Section 7 of the paper ("Formal Verification").
- Figures in Section 8 ("Verification Metrics") were generated from TLC state counts and Coq proof times; the raw scripts are omitted as they are reproducible from the above files.
- The Coq development is modular and can be extended to additional μACP encodings.

Contact
-------
For questions, please contact the authors.
