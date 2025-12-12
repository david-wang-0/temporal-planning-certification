fun main () =
    (
      CertificateConversionTest.check "CertConv";
      CertificateConversionTest8.check "CertConv8Bit";
      CertificateConversionTest32.check "CertConv32Bit";
      CertificateConversionTest64.check "CertConv64Bit"
    ) handle _ => "TESTS Failed XXX !!!\n" ^
                  "Some unhandled Exception was thrown!\n"
                  |> print

val _ = if MLton.isMLton then main() else ()