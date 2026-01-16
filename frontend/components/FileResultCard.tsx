import { useState } from "react";
import { motion, AnimatePresence } from "framer-motion";
import { ChevronDown, ChevronUp, FileCode } from "lucide-react";
import CodeEditor from "./CodeEditor"; // Assuming this is in the same folder or adjust import

interface FileResult {
    filename: string;
    status: string;
    verified: boolean; // Initial verification status
    fix_verified: boolean; // Final verification status (of the fix)
    original_code: string;
    fixed_code: string;
    logs: string[];
}

export default function FileResultCard({ result }: { result: FileResult }) {
    const [expanded, setExpanded] = useState(false);

    // Derived Status Logic
    // 1. SECURE: Originally verified.
    const isSecure = result.verified;

    // 2. PATCHED: Not originally verified, but the fixed code IS verified.
    const isPatched = !result.verified && result.fix_verified && result.fixed_code && result.fixed_code !== result.original_code;

    // 3. VULNERABLE: Not verified initially, and fix not verified (or failed).
    const isVulnerable = !isSecure && !isPatched;

    const getStatusBadge = () => {
        if (isSecure) {
            return (
                <span className="px-3 py-1 rounded-full text-xs font-bold bg-green-900/50 text-green-400 border border-green-800">
                    SECURE
                </span>
            );
        }
        if (isPatched) {
            return (
                <span className="px-3 py-1 rounded-full text-xs font-bold bg-yellow-900/50 text-yellow-400 border border-yellow-800">
                    AUTO-PATCHED
                </span>
            );
        }
        return (
            <span className="px-3 py-1 rounded-full text-xs font-bold bg-red-900/50 text-red-400 border border-red-800">
                VULNERABLE
            </span>
        );
    };

    return (
        <div className="bg-gray-900 border border-gray-800 rounded-xl overflow-hidden transition-all duration-300 hover:border-gray-700">
            <div
                className="p-4 flex items-center justify-between cursor-pointer"
                onClick={() => setExpanded(!expanded)}
            >
                <div className="flex items-center space-x-4">
                    <FileCode className={`w-6 h-6 ${isSecure ? 'text-green-400' : isPatched ? 'text-yellow-400' : 'text-red-400'}`} />
                    <h3 className="text-lg font-bold text-gray-200">{result.filename}</h3>
                </div>

                <div className="flex items-center space-x-4">
                    {getStatusBadge()}
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
                                label="ORIGINAL [PYTHON]"
                                value={result.original_code}
                                readOnly={true}
                            />
                            {/* If Secure, we might not have a fix, so show original or say "No changes needed" */}
                            <CodeEditor
                                label={isSecure ? "VERIFIED CODE" : isPatched ? "VERIFIED FIX" : "FAILED FIX ATTEMPT"}
                                value={isSecure ? result.original_code : result.fixed_code}
                                readOnly={true}
                            />
                        </div>
                        <div className="p-4 bg-black/50 border-t border-gray-800 text-xs text-gray-400 font-mono">
                            <p className="mb-2 font-bold text-gray-300">AUDIT LOGS:</p>
                            {result.logs.slice(-5).map((log: string, i: number) => (
                                <div key={i}>&gt; {log}</div>
                            ))}
                        </div>
                    </motion.div>
                )}
            </AnimatePresence>
        </div>
    );
}
