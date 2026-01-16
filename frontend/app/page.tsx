"use client";

import { useState } from "react";
import { motion, AnimatePresence } from "framer-motion";
import Header from "../components/Header";
import StatusBanner from "../components/StatusBanner";
import CodeEditor from "../components/CodeEditor";
import ThinkingProcess from "../components/ThinkingProcess"; // New Component
import FileResultCard from "../components/FileResultCard";
import { ChevronDown, ChevronUp, Github, FileCode } from "lucide-react";

export default function Home() {
  const [mode, setMode] = useState<"single" | "repo">("single");
  const [status, setStatus] = useState<"unverified" | "verified" | "failed" | "scanning" | "patched">("unverified");
  const [isLoading, setIsLoading] = useState(false);

  // Single File State
  const [code, setCode] = useState<string>("");
  const [verifiedCode, setVerifiedCode] = useState<string>("");

  // Repo State
  const [repoUrl, setRepoUrl] = useState<string>("");
  const [repoResults, setRepoResults] = useState<any[]>([]);

  // Shared Thinking State
  const [thinkingLogs, setThinkingLogs] = useState<{ status: string; message: string }[]>([]);

  const runSingleVerification = async () => {
    setStatus("scanning");
    setIsLoading(true);
    setThinkingLogs([]);
    setVerifiedCode("");

    try {
      const baseUrl = process.env.NEXT_PUBLIC_API_URL || "http://127.0.0.1:8000";
      const response = await fetch(`${baseUrl}/audit`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ python_code: code })
      });

      if (!response.body) throw new Error("No response body");
      const reader = response.body.getReader();
      const decoder = new TextDecoder();

      while (true) {
        const { done, value } = await reader.read();
        if (done) break;

        const chunk = decoder.decode(value);
        const lines = chunk.split("\n").filter(line => line.trim() !== "");

        for (const line of lines) {
          try {
            const event = JSON.parse(line);

            if (event.type === "result" || event.status === "success" || event.status === "verified" || event.status === "failed") {
              // Handle result (supporting both old 'success' schema if lingering, and new 'result' type)
              const resultData = event.result || event;
              const isVerified = resultData.status === "verified";
              // Smart Status: If failed but we have fixed code (that is newly generated), show Patched
              const isPatched = !isVerified && resultData.fixed_code && resultData.fixed_code.length > 0;

              if (isVerified) {
                setStatus("verified");
              } else if (isPatched) {
                setStatus("patched");
              } else {
                setStatus("failed");
              }

              setVerifiedCode(resultData.fixed_code || "");
              setThinkingLogs(prev => [...prev, { status: "success", message: "Verification Protocol Complete." }]);
            } else if (event.type === "log" || event.status) {
              // Handle log
              const status = event.status || "working";
              const message = event.message || "Processing...";
              setThinkingLogs(prev => [...prev, { status, message }]);
            }
          } catch (e) {
            console.error("Error parsing stream:", e);
          }
        }
      }
    } catch (error) {
      console.error(error);
      setStatus("failed");
      setThinkingLogs(prev => [...prev, { status: "error", message: "Connection Terminated Unexpectedly." }]);
    } finally {
      setIsLoading(false);
    }
  };

  const runRepoVerification = async () => {
    setStatus("scanning");
    setIsLoading(true);
    setThinkingLogs([]);
    setRepoResults([]);

    try {
      const baseUrl = process.env.NEXT_PUBLIC_API_URL || "http://127.0.0.1:8000";
      const response = await fetch(`${baseUrl}/audit_repo`, {
        method: "POST",
        headers: { "Content-Type": "application/json" },
        body: JSON.stringify({ repo_url: repoUrl })
      });

      if (!response.body) throw new Error("No response body");
      const reader = response.body.getReader();
      const decoder = new TextDecoder();

      while (true) {
        const { done, value } = await reader.read();
        if (done) break;

        const chunk = decoder.decode(value);
        const lines = chunk.split("\n").filter(line => line.trim() !== "");

        for (const line of lines) {
          try {
            const event = JSON.parse(line);

            if (event.type === "file_start") {
              setThinkingLogs(prev => [...prev, { status: "scanning", message: `Analyzing ${event.filename}...` }]);
            } else if (event.type === "result") {
              // Individual File Result
              setRepoResults(prev => [...prev, event.result]);
              setThinkingLogs(prev => [...prev, { status: "success", message: `File Verified: ${event.filename}` }]);
            } else if (event.type === "complete") {
              // Full Scan Complete
              setStatus("verified"); // Or patched/mixed if we want distinct repo statuses
              setThinkingLogs(prev => [...prev, { status: "success", message: "Repository Audit Complete." }]);
            } else if (event.type === "log") {
              setThinkingLogs(prev => [...prev, { status: event.status, message: event.message }]);
            } else if (event.type === "error") {
              setStatus("failed");
              setThinkingLogs(prev => [...prev, { status: "error", message: event.message }]);
            }
          } catch (e) {
            console.error("Error parsing stream:", e);
          }
        }
      }
    } catch (error) {
      console.error(error);
      setStatus("failed");
      setThinkingLogs(prev => [...prev, { status: "error", message: "Repository Audit Failed." }]);
    } finally {
      setIsLoading(false);
    }
  };

  return (
    <main className="min-h-screen bg-black text-white font-mono flex flex-col">
      <Header />
      <StatusBanner status={status} isLoading={isLoading} />

      {/* Mode Toggle */}
      <div className="flex justify-center py-6">
        <div className="bg-gray-900 p-1 rounded-lg flex border border-gray-800">
          <button
            onClick={() => setMode("single")}
            className={`px-6 py-2 rounded-md transition-all duration-300 ${mode === "single" ? "bg-blue-600 text-white shadow-lg shadow-blue-500/50" : "text-gray-400 hover:text-white"}`}
          >
            Single File
          </button>
          <button
            onClick={() => setMode("repo")}
            className={`px-6 py-2 rounded-md transition-all duration-300 ${mode === "repo" ? "bg-purple-600 text-white shadow-lg shadow-purple-500/50" : "text-gray-400 hover:text-white"}`}
          >
            Repository
          </button>
        </div>
      </div>

      <div className="flex-1 px-8 pb-8 flex flex-col space-y-6">

        {/* Single File Mode */}
        {mode === "single" && (
          <div className="grid grid-cols-2 gap-8 flex-1">
            <CodeEditor
              label="VULNERABLE CODE [PYTHON]"
              value={code}
              onChange={setCode}
              readOnly={false}
            />
            <div className="flex flex-col space-y-6 h-full">
              <CodeEditor
                label="VERIFIED CODE [LEAN 4]"
                value={verifiedCode}
                readOnly={true}
              />
              {/* Replaced Console with ThinkingProcess */}
              <ThinkingProcess logs={thinkingLogs} isLoading={isLoading} />
            </div>
          </div>
        )}

        {/* Repo Mode */}
        {mode === "repo" && (
          <div className="flex flex-col space-y-8 max-w-5xl mx-auto w-full">
            {/* URL Input */}
            <div className="bg-gray-900 border border-gray-800 p-6 rounded-xl shadow-2xl">
              <div className="flex items-center space-x-4">
                <Github className="w-8 h-8 text-gray-400" />
                <input
                  type="text"
                  placeholder="https://github.com/username/repo"
                  className="flex-1 bg-black border border-gray-700 rounded-lg px-4 py-3 focus:outline-none focus:border-purple-500 text-lg transition-colors"
                  value={repoUrl}
                  onChange={(e) => setRepoUrl(e.target.value)}
                />
              </div>
            </div>

            {/* Thinking Process for Repo Mode */}
            <ThinkingProcess logs={thinkingLogs} isLoading={isLoading} />

            {/* File Cards */}
            <div className="space-y-4">
              {repoResults.map((result, idx) => (
                <FileResultCard key={idx} result={result} />
              ))}
            </div>
          </div>
        )}

      </div>

      <div className="p-8 border-t border-gray-800 flex justify-center">
        <button
          onClick={mode === "single" ? runSingleVerification : runRepoVerification}
          className={`
                        relative group px-8 py-4 bg-transparent border border-white/20 rounded-full 
                        overflow-hidden transition-all duration-300 hover:border-white/50 hover:shadow-[0_0_30px_rgba(255,255,255,0.1)]
                    `}
        >
          <div className={`absolute inset-0 opacity-20 ${mode === "single" ? "bg-gradient-to-r from-blue-600 to-purple-600" : "bg-gradient-to-r from-purple-600 to-pink-600"} group-hover:opacity-30 transition-opacity`} />
          <span className="relative font-bold tracking-widest text-lg">
            {isLoading ? "SCANNING TARGET..." : mode === "single" ? "RUN FORMAL VERIFICATION" : "INITIATE REPO AUDIT"}
          </span>
        </button>
      </div>

      <footer className="py-4 text-center text-gray-600 text-sm border-t border-gray-900">
        Argus v1.0 // Gemini 3 Powered
      </footer>
    </main>
  );
}


