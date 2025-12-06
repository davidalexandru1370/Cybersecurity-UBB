package com.example.backend.presentation.entities.response;

public class BaseResponse<T> {
    private T payload;
    private int statusCode;

    public BaseResponse(T payload, int statusCode) {
        this.payload = payload;
        this.statusCode = statusCode;
    }

    public T getPayload() {
        return payload;
    }

    public int getStatusCode() {
        return statusCode;
    }
}
