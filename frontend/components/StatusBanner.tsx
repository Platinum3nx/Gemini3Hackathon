"use client";

import { motion } from "framer-motion";
import { CheckCircle, AlertOctagon, Loader2 } from "lucide-react";

interface StatusBannerProps {
    status: "unverified" | "verified" | "failed" | "scanning" | "patched";
    isLoading?: boolean;
}

export default function StatusBanner({ status, isLoading }: StatusBannerProps) {
    const config = {
        unverified: {
            color: "bg-red-700",
            text: "SYSTEM STATUS: AWAITING TARGET",
            icon: AlertOctagon,
        },
        verified: {
            color: "bg-emerald-600",
            text: "MATHEMATICALLY PROVEN",
            icon: CheckCircle,
        },
        failed: {
            color: "bg-red-600",
            text: "VERIFICATION FAILED",
            icon: AlertOctagon,
        },
        patched: {
            color: "bg-yellow-600",
            text: "VULNERABILITY PATCHED (PROOF PENDING)",
            icon: CheckCircle,
        },
        scanning: {
            color: "bg-blue-600",
            text: "ARGUS SCANNING...",
            icon: Loader2,
        },
    };

    // If loading, force scanning view, otherwise use status
    const effectiveStatus = isLoading ? "scanning" : status;
    // Fallback if status is invalid or not in config (though TS prevents this mostly)
    const current = config[effectiveStatus] || config["unverified"];
    const Icon = current.icon;

    return (
        <motion.div
            className={`${current.color} w-full py-4 px-6 flex items-center justify-center space-x-3 text-white font-bold text-xl shadow-lg transition-colors duration-500`}
            initial={{ opacity: 0, y: -20 }}
            animate={{ opacity: 1, y: 0 }}
        >
            <Icon className={`w-8 h-8 ${effectiveStatus === "scanning" ? "animate-spin" : ""}`} />
            <span>{current.text}</span>
        </motion.div>
    );
}
