"use client";

import { useState } from "react";
import axios from "axios";
import { motion, AnimatePresence } from "framer-motion";
import Header from "../components/Header";
import StatusBanner from "../components/StatusBanner";
import CodeEditor from "../components/CodeEditor";
import LoggingConsole from "../components/Console";
import { CheckCircle, AlertOctagon, ChevronDown, ChevronUp, Github, FileCode } from "lucide-react";

export default function Home() {
  const [mode, setMode] = useState<"single" | "repo">("single");
  const [status, setStatus] = useState<"unverified" | "verified" | "failed" | "scanning">("unverified");

  // Single File State
  const [code, setCode] = useState<string>("");
  const [verifiedCode, setVerifiedCode] = useState<string>("");
  const [logs, setLogs] = useState<string[]>([]);

  // Repo State
  const [repoUrl, setRepoUrl] = useState<string>("");
  const [repoResults, setRepoResults] = useState<any[]>([]);

  const runSingleVerification = async () => {
    setStatus("scanning");
    setLogs(["Initiating Argus Audit Protocol..."]);
    setVerifiedCode("");

    try {
      const response = await axios.post("http://127.0.0.1:8000/audit", {
        python_code: code
      });

      const data = response.data;
      if (data.status === "verified") {
        setStatus("verified");
        setVerifiedCode(data.fixed_code);
        setLogs(prev => [...prev, ...data.logs, "Verification Complete. System Secure."]);
      } else {
        setStatus("failed");
        setLogs(prev => [...prev, ...data.logs, "Verification Failed. Manual Intervention Required."]);
      }
    } catch (error) {
      console.error(error);
      setStatus("failed");
      setLogs(prev => [...prev, "Critical Error: Connection to verification engine lost."]);
    }
  };

  const runRepoVerification = async () => {
    setStatus("scanning");
    setLogs([`Cloning repository: ${repoUrl}...`, "Analyzing file structure...", "Triaging critical files..."]);
    setRepoResults([]);

    try {
      const response = await axios.post("http://127.0.0.1:8000/audit_repo", {
        repo_url: repoUrl
      });

      const data = response.data;
      if (data.status === "complete") {
        setRepoResults(data.results);
        setStatus("verified"); // Or 'complete'
        setLogs(prev => [...prev, "Repository Scan Complete."]);
      } else {
        setStatus("failed");
        setLogs(prev => [...prev, `Scan Failed: ${data.message}`]);
      }
    } catch (error) {
      console.error(error);
      setStatus("failed");
      setLogs(prev => [...prev, "Critical Error: Repository audit failed."]);
    }
  };

  return (
    <main className="min-h-screen bg-black text-white font-mono flex flex-col">
      <Header />
      <StatusBanner status={status} />

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
              title="VULNERABLE CODE [PYTHON]"
              code={code}
              onChange={setCode}
              readOnly={false}
            />
            <div className="flex flex-col space-y-6 h-full">
              <CodeEditor
                title="VERIFIED CODE [LEAN 4]"
                code={verifiedCode}
                readOnly={true}
                isVerified={true}
              />
              <LoggingConsole logs={logs} />
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

            {/* File Cards */}
            <div className="space-y-4">
              {repoResults.map((result, idx) => (
                <FileResultCard key={idx} result={result} />
              ))}
            </div>

            <LoggingConsole logs={logs} />
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
            {status === "scanning" ? "SCANNING TARGET..." : mode === "single" ? "RUN FORMAL VERIFICATION" : "INITIATE REPO AUDIT"}
          </span>
        </button>
      </div>

      <footer className="py-4 text-center text-gray-600 text-sm border-t border-gray-900">
        Argus v1.0 // Gemini 3 Powered
      </footer>
    </main>
  );
}

function FileResultCard({ result }: { result: any }) {
  const [expanded, setExpanded] = useState(false);
  const isVerified = result.status === "verified";

  return (
    <div className="bg-gray-900 border border-gray-800 rounded-xl overflow-hidden transition-all duration-300 hover:border-gray-700">
      <div
        className="p-4 flex items-center justify-between cursor-pointer"
        onClick={() => setExpanded(!expanded)}
      >
        <div className="flex items-center space-x-4">
          <FileCode className="w-6 h-6 text-blue-400" />
          <h3 className="text-lg font-bold text-gray-200">{result.filename}</h3>
        </div>

        <div className="flex items-center space-x-4">
          <span className={`px-3 py-1 rounded-full text-xs font-bold ${isVerified ? "bg-green-900/50 text-green-400 border border-green-800" : "bg-red-900/50 text-red-400 border border-red-800"}`}>
            {result.status.toUpperCase()}
          </span>
          {expanded ? <ChevronUp className="w-5 h-5 text-gray-500" /> : <ChevronDown className="w-5 h-5 text-gray-500" />}
        </div>
      </div>

      <AnimatePresence>
        {expanded && (
          <motion.div
            initial={{ height: 0, opacity: 0 }}
            animate={{ height: "auto", opacity: 1 }}
            exit={{ height: 0, opacity: 0 }}
            className="border-t border-gray-800"
          >
            <div className="grid grid-cols-2 gap-4 p-4 h-96">
              <CodeEditor
                title="ORIGINAL"
                code={result.original_code}
                readOnly={true}
              />
              <CodeEditor
                title={isVerified ? "VERIFIED FIX" : "FAILED FIX"}
                code={result.fixed_code}
                readOnly={true}
                isVerified={isVerified}
              />
            </div>
            <div className="p-4 bg-black/50 border-t border-gray-800 text-xs text-gray-400 font-mono">
              <p className="mb-2 font-bold text-gray-300">AUDIT LOGS:</p>
              {result.logs.slice(-3).map((log: string, i: number) => (
                <div key={i}>&gt; {log}</div>
              ))}
            </div>
          </motion.div>
        )}
      </AnimatePresence>
    </div>
  )
}
