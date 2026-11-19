# strip Lean block comments (/- ... -/, nesting-aware) and line comments (-- ...) ; print "file:line:code" for non-empty remaining code
BEGIN { depth = 0 }
FNR == 1 { depth = 0 }
{
  line = $0; out = ""; i = 1; n = length(line)
  while (i <= n) {
    two = substr(line, i, 2)
    if (depth > 0) {
      if (two == "/-") { depth++; i += 2 }
      else if (two == "-/") { depth--; i += 2 }
      else i++
    } else {
      if (two == "/-") { depth++; i += 2 }
      else if (two == "--") { break }
      else { out = out substr(line, i, 1); i++ }
    }
  }
  if (out ~ /[^ \t]/) print FILENAME ":" FNR ":" out
}
