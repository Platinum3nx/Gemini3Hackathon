"use client";

import { motion } from "framer-motion";
import { CheckCircle, AlertOctagon, Loader2 } from "lucide-react";

interface StatusBannerProps {
    status: "unverified" | "verified" | "failed" | "scanning";
}

export default function StatusBanner({ status }: StatusBannerProps) {
    const config = {
        unverified: {
            color: "bg-red-600",
            text: "UNVERIFIED / VULNERABLE",
            icon: AlertOctagon,
        },
        verified: {
            color: "bg-green-600",
            text: "MATHEMATICALLY PROVEN",
            icon: CheckCircle,
        },
        failed: {
            color: "bg-yellow-600",
            text: "VERIFICATION FAILED",
            icon: AlertOctagon,
        },
        scanning: {
            color: "bg-blue-600",
            text: "VERITAS AI SCANNING...",
            icon: Loader2,
        },
    };

    const current = config[status];
    const Icon = current.icon;

    return (
        <motion.div
            className={`${current.color} w-full py-4 px-6 flex items-center justify-center space-x-3 text-white font-bold text-xl shadow-lg transition-colors duration-500`}
            initial={{ opacity: 0, y: -20 }}
            animate={{ opacity: 1, y: 0 }}
        >
            <Icon className={`w-8 h-8 ${status === "scanning" ? "animate-spin" : ""}`} />
            <span>{current.text}</span>
        </motion.div>
    );
}
