-- This module serves as the root of the `FastMultiplication` library.
-- Import modules here that should be built as part of the library.
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Workspace
import FastMultiplication.ShorVerification.Implementation.Shor.Proofs.Correctness
import FastMultiplication.ShorVerification.Implementation.Shor.Main
import FastMultiplication.ShorVerification.Implementation.PhaseProduct.Main
import FastMultiplication.ShorVerification.Implementation.QFT.Main
import FastMultiplication.ShorVerification.Implementation.ModularExponentiation.Main
import FastMultiplication.ShorVerification.Implementation.GateCount.QFT_GateCount
import FastMultiplication.ShorVerification.Implementation.GateCount.Shor_GateCount
import FastMultiplication.ShorVerification.Framework.Submission
import FastMultiplication.ShorVerification.Implementation.Reference.ReferenceShorImplementation
