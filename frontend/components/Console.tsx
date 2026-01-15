"use client";

import { useEffect, useRef } from "react";
import { motion } from "framer-motion";

interface ConsoleProps {
    logs: string[];
}

export default function Console({ logs }: ConsoleProps) {
    const scrollRef = useRef<HTMLDivElement>(null);

    useEffect(() => {
        if (scrollRef.current) {
            scrollRef.current.scrollTop = scrollRef.current.scrollHeight;
        }
    }, [logs]);

    return (
        <div className="bg-black text-green-400 font-mono p-4 h-64 overflow-y-auto rounded-lg shadow-inner border border-green-900" ref={scrollRef}>
            <div className="flex flex-col space-y-1">
                {logs.map((log, i) => (
                    <motion.div
                        key={i}
                        initial={{ opacity: 0, x: -10 }}
                        animate={{ opacity: 1, x: 0 }}
                        transition={{ duration: 0.3 }}
                    >
                        <span className="opacity-50 mr-2">{">"}</span>
                        {log}
                    </motion.div>
                ))}
                {logs.length === 0 && <span className="opacity-50 italic">Ready for verification...</span>}
            </div>
        </div>
    );
}
