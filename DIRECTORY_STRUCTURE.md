# Create all directories
mkdir -p coq/theories
mkdir -p src
mkdir -p cli/bin
mkdir -p tests/{unit,integration,property}
mkdir -p benchmarks
mkdir -p examples/{basic-policy-application,unicode-attack-prevention,audit-trail-reconstruction}
mkdir -p docs/architecture
mkdir -p docker
mkdir -p .github/{workflows,ISSUE_TEMPLATE}

# Verify structure
tree -L 2
