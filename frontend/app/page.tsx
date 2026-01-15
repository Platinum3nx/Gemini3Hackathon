"use client";

import { useState } from "react";
import axios from "axios";
import Header from "@/components/Header";
import StatusBanner from "@/components/StatusBanner";
import CodeEditor from "@/components/CodeEditor";
import Console from "@/components/Console";
import { Play } from "lucide-react";

/* 
  Initial Example Code: A classic "Bank Transfer" bug.
  It allows transferring more money than available (negative balance) 
  if not caught by simple checks, or integer overflow in some languages 
  (though Python handles large ints, the logic error is the focus).
*/
const INITIAL_CODE = `def transfer_funds(sender_balance, amount):
    # Retrieve user balance
    if sender_balance > 0:
        # Subtle bug: What if amount > sender_balance?
        new_balance = sender_balance - amount
        return new_balance
    return sender_balance`;

export default function Home() {
  const [code, setCode] = useState(INITIAL_CODE);
  const [verifiedCode, setVerifiedCode] = useState("");
  const [logs, setLogs] = useState<string[]>([]);
  const [status, setStatus] = useState<"unverified" | "verified" | "failed" | "scanning">("unverified");
  const [isHovered, setIsHovered] = useState(false);

  const runVerification = async () => {
    setStatus("scanning");
    setLogs(["Initiating Veritas AI audit...", "Connecting to Gemini 3.0 Pro..."]);
    setVerifiedCode("");

    try {
      // Simulate "Streaming" effect for initial connection
      await new Promise(r => setTimeout(r, 800));

      const response = await axios.post("http://localhost:8000/audit", {
        python_code: code
      });

      const result = response.data;

      // Animate logs appearing one by one (fast)
      let currentLogs = [...logs];
      for (const log of result.logs) {
        currentLogs.push(log);
        setLogs([...currentLogs]);
        await new Promise(r => setTimeout(r, 300)); // nice typing effect
      }

      if (result.status === "verified") {
        setStatus("verified");
        setVerifiedCode(result.fixed_code);
        setLogs(prev => [...prev, "✓ Verification Successful. Proof Constructed."]);
      } else {
        setStatus("failed");
        setLogs(prev => [...prev, "✗ Verification Failed. Manual Review Required."]);
      }

    } catch (error) {
      console.error(error);
      setStatus("failed");
      setLogs(prev => [...prev, "Error connecting to verification server."]);
    }
  };

  return (
    <div className="min-h-screen bg-gray-950 text-gray-100 font-sans flex flex-col">
      <Header />

      <StatusBanner status={status} />

      <main className="flex-1 p-6 flex gap-6 overflow-hidden">
        {/* Left Column: Vulnerable Source */}
        <div className="flex-1 flex flex-col min-w-0 bg-gray-900/50 rounded-xl border border-gray-800 p-6 shadow-2xl backdrop-blur-sm">
          <CodeEditor
            label="Vulnerable Source (Python)"
            value={code}
            onChange={setCode}
          />

          <div className="mt-6 flex justify-end">
            <button
              onClick={runVerification}
              disabled={status === "scanning"}
              onMouseEnter={() => setIsHovered(true)}
              onMouseLeave={() => setIsHovered(false)}
              className={`
                 relative px-8 py-4 rounded-lg font-bold text-lg tracking-wide shadow-lg
                 transition-all duration-300 transform
                 ${status === "scanning"
                  ? "bg-gray-700 cursor-wait opacity-50"
                  : "bg-gradient-to-r from-blue-600 to-indigo-600 hover:from-blue-500 hover:to-indigo-500 hover:scale-[1.02] hover:shadow-blue-900/50 ring-2 ring-blue-500/20"
                }
               `}
            >
              <div className="flex items-center space-x-3">
                <Play className={`w-5 h-5 ${status === "scanning" ? "hidden" : "fill-current"}`} />
                <span>{status === "scanning" ? "SCANNING..." : "RUN FORMAL VERIFICATION"}</span>
              </div>

              {/* Button Glow Effect */}
              {isHovered && status !== "scanning" && (
                <div className="absolute inset-0 rounded-lg bg-blue-400 opacity-20 blur-md transition-opacity"></div>
              )}
            </button>
          </div>
        </div>

        {/* Right Column: Verified Kernel */}
        <div className="flex-1 flex flex-col min-w-0 space-y-6">
          {/* Top: Verified Code */}
          <div className="flex-1 bg-gray-900/50 rounded-xl border border-gray-800 p-6 shadow-2xl backdrop-blur-sm relative overflow-hidden">
            <CodeEditor
              label="Verified Kernel (Python + Lean Proof)"
              value={verifiedCode}
              readOnly={true}
            />

            {/* Blur overlay if not verified yet to create mystery */}
            {status === "unverified" || status === "scanning" ? (
              <div className="absolute inset-0 bg-gray-950/80 backdrop-blur-sm flex items-center justify-center border border-gray-800 rounded-lg m-1 z-10">
                <div className="text-gray-500 font-mono text-sm tracking-widest uppercase">
                  {status === "scanning" ? "Synthesizing Proof..." : "Waiting for Verification"}
                </div>
              </div>
            ) : null}
          </div>

          {/* Bottom: Console */}
          <div className="h-1/3 min-h-[200px]">
            <Console logs={logs} />
          </div>
        </div>
      </main>
    </div>
  );
}
