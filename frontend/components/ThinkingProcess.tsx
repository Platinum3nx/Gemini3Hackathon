
import { motion, AnimatePresence } from "framer-motion";
import { Loader2, CheckCircle, XCircle, Terminal } from "lucide-react";
import { useEffect, useRef } from "react";

interface ThinkingProcessProps {
    logs: { status: string; message: string }[];
    isLoading?: boolean;
}

export default function ThinkingProcess({ logs, isLoading }: ThinkingProcessProps) {
    const bottomRef = useRef<HTMLDivElement>(null);

    useEffect(() => {
        bottomRef.current?.scrollIntoView();
    }, [logs]);

    const getIcon = (status: string, isActive: boolean) => {
        if (isActive) {
            return <Loader2 className="w-4 h-4 animate-spin text-blue-400" />;
        }
        switch (status) {
            case "translating":
            case "verifying":
            case "fixing":
            case "scanning":
                // If not active (i.e. history), show a checkmark or dot
                return <CheckCircle className="w-4 h-4 text-gray-600" />;
            case "failed":
            case "error":
                return <XCircle className="w-4 h-4 text-red-500" />;
            case "success":
                return <CheckCircle className="w-4 h-4 text-green-500" />;
            default:
                return <Terminal className="w-4 h-4 text-gray-500" />;
        }
    };

    return (
        <div className="bg-black/80 border border-gray-800 rounded-lg p-4 font-mono text-sm shadow-inner max-h-60 overflow-y-auto w-full">
            <div className="flex items-center space-x-2 text-gray-400 mb-2 border-b border-gray-800 pb-2">
                <Terminal className="w-4 h-4" />
                <span className="text-xs uppercase tracking-widest">Argus Neural Link</span>
            </div>

            <div className="space-y-2">
                <AnimatePresence initial={false}>
                    {logs.map((log, idx) => {
                        const isActive = !!isLoading && idx === logs.length - 1;
                        return (
                            <motion.div
                                key={idx}
                                initial={{ opacity: 0, x: -10 }}
                                animate={{ opacity: 1, x: 0 }}
                                className="flex items-start space-x-3"
                            >
                                <div className="mt-1">{getIcon(log.status, isActive)}</div>
                                <span className={`${log.status === "failed" ? "text-red-400" : log.status === "success" ? "text-green-400" : "text-gray-300"}`}>
                                    {log.message}
                                </span>
                            </motion.div>
                        );
                    })}
                </AnimatePresence>
                <div ref={bottomRef} />
            </div>
        </div>
    );
}
